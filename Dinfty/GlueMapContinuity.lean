import Dinfty.NormalizedGlueMap

open GluingTowerLibrary SierpinskiApplication

/-!
# Local continuity of `Φ`'s morphism action

Claim 3(b)'s ingredient 3 is that `Φ_tri_v2` is **locally continuous**: the
action on hom-sets, `g ↦ Φ(g)`, preserves directed suprema of morphisms.  In
the vault it is proved informally and priced in as *explicitly not
in-principle finitely machine-checkable* (`Results/03 Phi Gluing Functor`), so
no script can settle it.  Since Update 24 `Φ`'s morphism action exists in Lean
(`NormalizedGlueMap.glueMap`), so the statement can at last be made against a
definition instead of prose.  This module makes it, and proves the part that is
actually provable at this level.

## The observation that makes this tractable

`glueMap`'s **value** does not depend on its hypotheses:

    glueMap g m m' hginj hbot hmid htop hm0 x = ⟨baseMap g x.val, _⟩

The five hypotheses feed only the well-definedness proof (`canon_baseMap`).  So
the morphism action *as a function* is `baseMap g`, which is hypothesis-free,
and continuity in `g` can be stated without threading tripointedness and
injectivity through a directed family — which is what would otherwise make the
statement awkward, since a directed sup of injective maps need not be injective.

## What is proved here

1. **Monotone in the morphism** (`baseMap_leGlue_of_le`): `g ≤ g'` implies
   `baseMap g x ≤ baseMap g' x` in the glued order, at every `x` and for every
   marked point.  Hypothesis-free.  This is the half of local continuity that
   holds for structural reasons — `baseMap` is tagwise, so it inherits `g ≤ g'`
   inside each copy without ever consulting the gluing.
2. **Directed families over a finite index attain their sup**
   (`exists_greatest_of_directed`): standard, and the reason (3) is available.
3. **Local continuity at each finite level** (`baseMap_directed_sup`,
   `glueMap_directed_sup`): a directed family of morphisms indexed by a finite
   nonempty type has a greatest member, and `baseMap` carries it to the
   greatest member of the image family.  So the morphism action preserves
   directed sups **at every finite level of the tower**.

## What is NOT proved here, and must not be read into it

Every level of the normalized tower is finite (`TriLevel.fin`), so (3) is a
corollary of (1) *because directed sups in a finite poset are attained inside
the family*.  That is a real statement about the tower, and it is exactly the
statement Claim 3(b)'s ingredient 3 does **not** reduce to.

Ingredient 3 is local continuity of `Φ` as a functor on an **O-category of
dcpos** — sups of ω-chains of morphisms between the *bilimits*, where the
hom-cpos are not finite and sups are genuinely not attained.  Nothing here
touches that.  The honest summary is: the finite-level content of ingredient 3
is now machine-checked and is easy for a reason that does not generalise; the
limit content is untouched and is still the informal, not-finitely-checkable
part.

Filed this way deliberately.  Reporting (3) as "local continuity, formalized"
would be precisely the finite/limit conflation this project has logged four
times in [[Errors and Pitfalls]].

## A distinction worth keeping straight

Local continuity is about **directed** suprema, not binary joins.  `glueA_sup`
(`GluingTowerLibrary.lean:6681`) says copy `A` is closed under joins, and it
would be natural to chase `baseMap (g ⊔ g') = baseMap g ⊔ baseMap g'` from it
as a "stronger" result.  That is a different property, and it is **not** what
ingredient 3 requires:

* Scott-continuity = preserves directed sups.  For a directed family over a
  finite index the sup is a member of the family, which is why §3 is available
  from monotonicity alone.
* Binary join-preservation is a linearity condition.  It neither follows from
  nor implies Scott-continuity in general.

The distinction matters here beyond pedantry, because "join-preservation" is
also the name of a *different* obstruction in this project — the one that broke
`liftGen` and refuted `axiom PsiIso` (Updates 2-3), which concerns the
conjugation action on **elements** of the tower, not the functor's action on
**hom-sets**.  Proving binary join-preservation of `baseMap` would say nothing
about that obstruction and nothing about ingredient 3, while looking like
progress on both.  Not chased, on purpose.
-/

open scoped Classical

universe u v

namespace GlueMapContinuity

open NormalizedGlueMap

/-! ## 1. The morphism action is monotone in the morphism -/

section Monotone

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

/-- **`baseMap` is monotone in its morphism argument.**  `baseMap` is tagwise,
so a pointwise inequality between morphisms is carried into each copy
separately and never has to consult the gluing: the witness on both sides is
the point's own tag. -/
theorem baseMap_leGlue_of_le (m' : P') {g g' : P →o P'} (hgg : g ≤ g')
    (x : GlueBase P) :
    leGlue m' (baseMap g x) (baseMap g' x) := by
  have hpt : ∀ a : P, g a ≤ g' a := fun a => OrderHom.le_def.mp hgg a
  cases x with
  | inl a =>
    exact ⟨Sum.inl (g a), self_mem_occs _ _, Sum.inl (g' a), self_mem_occs _ _, hpt a⟩
  | inr x =>
    cases x with
    | inl a =>
      exact ⟨Sum.inr (Sum.inl (g a)), self_mem_occs _ _,
             Sum.inr (Sum.inl (g' a)), self_mem_occs _ _, hpt a⟩
    | inr a =>
      exact ⟨Sum.inr (Sum.inr (g a)), self_mem_occs _ _,
             Sum.inr (Sum.inr (g' a)), self_mem_occs _ _, hpt a⟩

/-- The same at the level of `Φ(g)` itself.  `GlueCar`'s `LE` instance is
definitionally `leGlue` on underlying values, and `glueMap`'s value is
`baseMap`, so this is `baseMap_leGlue_of_le` transported. -/
theorem glueMap_le_of_le {m : P} {m' : P'} {g g' : P →o P'} (hgg : g ≤ g')
    (hginj : Function.Injective g) (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m')
    (htop : g ⊤ = (⊤ : P')) (hm0 : m ≠ (⊥ : P))
    (hginj' : Function.Injective g') (hbot' : g' ⊥ = (⊥ : P')) (hmid' : g' m = m')
    (htop' : g' ⊤ = (⊤ : P')) (x : GlueCar (P := P) m) :
    glueMap g m m' hginj hbot hmid htop hm0 x
      ≤ glueMap g' m m' hginj' hbot' hmid' htop' hm0 x :=
  baseMap_leGlue_of_le m' hgg x.val

end Monotone

/-! ## 2. Directed families over a finite index attain their sup

The reason local continuity is available at finite levels at all.  Stated for a
general preorder — it is not about gluing. -/

section Attained

variable {α : Type u} [Preorder α] {ι : Type v} [Fintype ι] [Nonempty ι]

/-- A directed family indexed by a finite nonempty type has a **greatest
member**, inside the family.  Hence every monotone map preserves its
supremum — trivially, because the supremum is one of the values. -/
theorem exists_greatest_of_directed (f : ι → α) (hdir : Directed (· ≤ ·) f) :
    ∃ z : ι, ∀ i : ι, f i ≤ f z := by
  obtain ⟨z, hz⟩ := hdir.finset_le (Finset.univ : Finset ι)
  exact ⟨z, fun i => hz i (Finset.mem_univ i)⟩

end Attained

/-! ## 3. Local continuity at each finite level -/

section Continuity

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']
variable {ι : Type v} [Fintype ι] [Nonempty ι]

/-- **Local continuity of the morphism action, at a finite level.**  A directed
family of morphisms has a greatest member `g z`, and `baseMap (g z)` dominates
every `baseMap (g i)` — so it is the supremum of the image family, which is
what "preserves directed sups" says here.

Finiteness is doing the work: the sup is attained *inside* the family, so
monotonicity alone suffices.  That is why this does not generalise to the
bilimit, where hom-cpos are infinite and sups are not attained. -/
theorem baseMap_directed_sup (m' : P') (g : ι → (P →o P'))
    (hdir : Directed (· ≤ ·) g) :
    ∃ z : ι, (∀ i : ι, g i ≤ g z) ∧
      ∀ (i : ι) (x : GlueBase P), leGlue m' (baseMap (g i) x) (baseMap (g z) x) := by
  obtain ⟨z, hz⟩ := exists_greatest_of_directed g hdir
  exact ⟨z, hz, fun i x => baseMap_leGlue_of_le m' (hz i) x⟩

/-- The same for `Φ(g)`, for a family whose members all carry the tripointedness
and injectivity data.  The sup is `g z`, a member of the family, so its
hypotheses come from the family itself — no need to close the tripointed maps
under directed sups (they are not closed under it in general: a sup of
injective maps need not be injective, which is exactly why this is stated at a
member rather than at an abstract supremum). -/
theorem glueMap_directed_sup {m : P} {m' : P'} (hm0 : m ≠ (⊥ : P))
    (g : ι → (P →o P')) (hdir : Directed (· ≤ ·) g)
    (hginj : ∀ i, Function.Injective (g i)) (hbot : ∀ i, (g i) ⊥ = (⊥ : P'))
    (hmid : ∀ i, (g i) m = m') (htop : ∀ i, (g i) ⊤ = (⊤ : P')) :
    ∃ z : ι, ∀ (i : ι) (x : GlueCar (P := P) m),
      glueMap (g i) m m' (hginj i) (hbot i) (hmid i) (htop i) hm0 x
        ≤ glueMap (g z) m m' (hginj z) (hbot z) (hmid z) (htop z) hm0 x := by
  obtain ⟨z, hz, _⟩ := baseMap_directed_sup (P := P) m' g hdir
  exact ⟨z, fun i x => baseMap_leGlue_of_le m' (hz i) x.val⟩

end Continuity

/-! ## 4. The tower's levels are finite, so §3 applies at every level

`TriLevel` carries `Fintype` as a field, so the hypothesis §3 needs is
discharged at every level of the normalized tower by construction.  Recorded so
the applicability is a theorem rather than a remark. -/

section TowerLevels

open NormalizedGlueMap.NormalizedTower

/-- Every level of the normalized tower is finite — so `baseMap_directed_sup`
applies at each of them.  (`triLevelSucc` builds its `fin` field by
`inferInstance` from `GlueCar`'s subtype-of-a-`Fintype` instance.) -/
noncomputable instance triLevelFintype (k : ℕ) : Fintype (triLevel k).carrier :=
  (triLevel k).fin

end TowerLevels

end GlueMapContinuity
