import Dinfty.PhiTriIdentification
import Dinfty.NormalizedGlueMap
import Dinfty.EndPRigid
import Dinfty.TowerNoAbsorption

open GluingTowerLibrary SierpinskiApplication

/-!
# The bridge: `Φ_tri_v2` **is** the tower's step

§74–§75 built `Φ_tri_v2` over the `Gen` layer — arbitrary bounded `P`, no
finiteness — and every status note since has carried the caveat that this does
*not* reach the tower, because `D (k+1)` is built from the finite `GlueCar`
rather than from `GlueCarGen`.

**That caveat was unnecessary.**  The two constructions are not merely
isomorphic; they are the *same definition*, written twice with different ambient
instance requirements.  `GlueBase = GlueBaseGen`, `canon = canonGen`,
`rawRule = rawRuleGen`, `occs = occsGen`, `leGlue = leGlueGen`,
`GlueCar = GlueCarGen` — and therefore

```lean
D_succ_eq : D (k + 1) = GlueCarGen (P := EndP (D k)) (markedPt k) := rfl
```

Everything in this section down to `top_succ_eq` is `rfl`.  The `Gen` layer was
never a generalisation the tower had to be transported into; it was the tower,
stated without the instances it does not use.

## The identification, made literal

The tower has its own morphism action, `NormalizedGlueMap.glueMap`, and it is
built by **restriction** — `baseMap g` on the nose — which is exactly the route
§74 observed needs `g` to *reflect* `⊥` and the marked point.  `NormalizedGlueMap`
buys that reflection with **injectivity** (`map_eq_bot`, `map_eq_mid`).  So the
two constructions differ precisely as predicted:

| | `glueMap` (restriction) | `phiFun` (descent) |
|---|---|---|
| needs | `canon ∘ baseMap = baseMap ∘ canon` | `canon ∘ baseMap ∘ canon = canon ∘ baseMap` |
| bought with | injectivity of `g` | tripointedness alone |

and where both are defined they agree:

```lean
phiFun_eq_glueMap : Injective f.toFun → phiFun f = glueMap f.toFun …
```

**This is the identification of `baseMapGen` with `Φ_tri_v2`'s action**, at the
tower, as an equation between two maps that were defined independently.  `phiFun`
is the extension of `glueMap` to morphisms that are not injective.

## What this leaves

Nothing about ingredient 2 is informal, and nothing about it is stated only over
an abstract base.  What remains is what §75 named: the *uniqueness* of the action
is conditional on rigidity of the glue base `EndP (D k)` — true at `k = 0, 1`,
and CONJ′ beyond.
-/

universe u

namespace PhiTriTower

open PhiTriFunctor PhiTriIdentification GenContinuity TowerNoAbsorption

/-! ## The `Gen` layer is the finite layer -/

section Bridge

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

theorem canon_eq (m : P) : canon m = canonGen m := rfl
theorem glueCar_eq (m : P) : GlueCar (P := P) m = GlueCarGen (P := P) m := rfl
theorem rawRule_eq (m : P) : rawRule (P := P) m = rawRuleGen (P := P) m := rfl
theorem occs_eq (m : P) : occs (P := P) m = occsGen (P := P) m := rfl
theorem leGlue_eq (m : P) : leGlue (P := P) m = leGlueGen (P := P) m := rfl

theorem baseMap_eq (g : P →o P') :
    NormalizedGlueMap.baseMap g = baseMapGen g := by
  funext x
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl b => rfl
    | inr c => rfl

/-- **The identification.**  The descent and the restriction agree wherever the
restriction is defined — i.e. for injective `f`. -/
theorem phiFun_eq_glueMap {m : P} {m' : P'} (f : TriHom m m')
    (hinj : Function.Injective f.toFun) (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt'
      = NormalizedGlueMap.glueMap f.toFun m m' hinj f.map_bot f.map_mark
          f.map_top hm := by
  funext x
  refine Subtype.ext ?_
  show canonGen m' (baseMapGen f.toFun x.1) = NormalizedGlueMap.baseMap f.toFun x.1
  rw [← baseMap_eq f.toFun]
  show canon m' (NormalizedGlueMap.baseMap f.toFun x.1)
    = NormalizedGlueMap.baseMap f.toFun x.1
  rw [NormalizedGlueMap.canon_baseMap f.toFun m m' hinj f.map_bot f.map_mark
        f.map_top hm x.1]
  exact congrArg (NormalizedGlueMap.baseMap f.toFun) x.2

end Bridge

/-! ## The tower -/

section Tower

-- `towerLevelSucc` bakes `endPDecidableEq` into `D (k+1)`; Mathlib's
-- `OrderHom.instDecidableEqOfForall` would be a different, non-defeq choice.
attribute [local instance 2000] endPDecidableEq

/-- The tower's own tripointed morphisms. -/
abbrev TowerHom (k k' : ℕ) : Type := TriHom (markedPt k) (markedPt k')

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ### The bridge at the tower — all `rfl` -/

theorem D_succ_eq (k : ℕ) :
    D (k + 1) = GlueCarGen (P := EndP (D k)) (markedPt k) := rfl

theorem le_succ_eq (k : ℕ) (x y : D (k + 1)) :
    (x ≤ y) = leGlueGen (markedPt k) x.1 y.1 := rfl

theorem dMid_succ_eq (k : ℕ) : dMid (k + 1) = triMark (markedPt k) := rfl

theorem bot_succ_eq (k : ℕ) : (⊥ : D (k + 1)) = triBot (markedPt k) := rfl

/-- The one that is not `rfl`: `D (k+1)`'s top comes from `glueBoundedOrder`, so
it is identified with `tag_C ⊤` by antisymmetry rather than by unfolding. -/
theorem top_succ_eq (k : ℕ) :
    (⊤ : D (k + 1)) = (triTop (markedPt k) (hmtk k) (hbtk k) : D (k + 1)) := by
  refine le_antisymm ?_ le_top
  exact le_triTop (markedPt k) (hmtk k) (hbtk k) (⊤ : D (k + 1))

/-! ### `Φ` on the tower

`Fintype (EndP (D k))` is not globally synthesizable and the tower carries **two**
`DecidableEq (EndP (D k))` instances — `endPDecidableEq`, which `towerLevelSucc`
bakes into `D (k+1)`, and Mathlib's `OrderHom.instDecidableEqOfForall`, which is
what synthesis finds (`CopyBExclusion`'s note).  So the definitions below carry
**no type ascription**: unification reads the instances off `f` and off the
nondegeneracy hypotheses, exactly as `canonBFix` does, and the mismatch never
arises.  `phiTowerD` then *checks* that the result really is a map of tower
levels — it typechecks only because `D_succ_eq` holds definitionally. -/

/-- `EndP (D k)` is finite — via the injection into `D k → D k`, which needs no
`DecidableRel` and so does not disturb the `DecidableEq` the tower baked in. -/
noncomputable instance finiteEndPD (k : ℕ) : Finite (EndP (D k)) :=
  Finite.of_injective (fun f : EndP (D k) => (f : D k → D k))
    (fun _ _ h => OrderHom.ext _ _ h)

/-- **`Φ` on morphisms, at the tower.** -/
@[reducible] noncomputable def phiTower {k k' : ℕ} (f : TowerHom k k') :=
  phiFun f (hmk k') (hbtk k')

/-- **The action is a map of tower levels.**  This is the bridge at the morphism
level: it typechecks precisely because `D (k+1)` *is* `GlueCarGen (markedPt k)`. -/
noncomputable def phiTowerD {k k' : ℕ} (f : TowerHom k k') : D (k + 1) → D (k' + 1) :=
  phiTower f

theorem phiTower_id (k : ℕ) : phiTower (TriHom.id (markedPt k)) = id :=
  phiFun_id (markedPt k) (hmk k) (hbtk k)

theorem phiTower_comp {k k' k'' : ℕ} (f : TowerHom k k') (f' : TowerHom k' k'') :
    phiTower (f'.comp f) = phiTower f' ∘ phiTower f :=
  phiFun_comp f f' (hmk k') (hbtk k') (hmk k'') (hbtk k'')

theorem phiTower_monotone {k k' : ℕ} (f : TowerHom k k')
    {x y : GlueCarGen (P := EndP (D k)) (markedPt k)} (h : x ≤ y) :
    phiTower f x ≤ phiTower f y :=
  phiFun_monotone f (hmk k') (hmtk k') (hbtk k') h

theorem phiTower_triBot {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triBot (markedPt k)) = triBot (markedPt k') :=
  phiFun_triBot f (hmk k') (hbtk k')

theorem phiTower_triMark {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triMark (markedPt k)) = triMark (markedPt k') :=
  phiFun_triMark f (hmk k') (hbtk k')

theorem phiTower_triTop {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triTop (markedPt k) (hmtk k) (hbtk k))
      = triTop (markedPt k') (hmtk k') (hbtk k') :=
  phiFun_triTop f (hmtk k) (hbtk k) (hmk k') (hmtk k') (hbtk k')

/-- **The identification, at the tower.**  For injective `f`, `Φ`'s action is
the tower's own `glueMap`. -/
theorem phiTower_eq_glueMap {k k' : ℕ} [Fintype (EndP (D k))]
    [Fintype (EndP (D k'))] (f : TowerHom k k')
    (hinj : Function.Injective f.toFun) :
    phiTower f
      = NormalizedGlueMap.glueMap f.toFun (markedPt k) (markedPt k') hinj
          f.map_bot f.map_mark f.map_top (hmk k) :=
  phiFun_eq_glueMap f hinj (hmk k) (hmk k') (hbtk k')

/-- **Uniqueness of the action at the tower**, conditional on rigidity of the
glue base.  `EndP (D k)` is rigid at `k = 0` and `k = 1`; beyond that it is
CONJ′, not another computation. -/
theorem phiTower_unique_of_rigid (k : ℕ)
    (hrigid : Subsingleton (EndP (D k) ≃o EndP (D k)))
    (f : TowerHom k k) (hf : Function.Injective f.toFun)
    (ψ : EndP (D k) →o EndP (D k)) (hψ : Function.Injective ψ) :
    phiTwist f ψ (hmk k) (hbtk k) = phiTower f :=
  phiTwist_eq_phiFun_of_rigid hrigid f hf ψ hψ (hmk k) (hbtk k)

/-! ### The hypothesis discharged: `EndP (D k)` is rigid

`EndPRigid.endP_rigid` says a rigid finite lattice with a unique atom and coatom
has a rigid `EndP`.  `D_all_rigid` supplies the rigidity and
`realUniqueAtomCoatom` the atom, so the uniqueness above is **unconditional** —
what §73 called CONJ′ was `jh_free` all along. -/

/-- `lamD k` is join-irreducible — the witness that `J (D k)` is nonempty.
(`joinIrred_atomOf` cannot serve: it presupposes the very nonemptiness.) -/
theorem joinIrred_lamD (k : ℕ) : JoinIrred (D k) (lamD k) := by
  refine ⟨lamD_ne_bot k, fun b c hbc => ?_⟩
  by_cases hb : b = (⊥ : D k)
  · subst hb; right; simpa using hbc
  · left
    have hble : b ≤ lamD k := hbc ▸ le_sup_left
    exact le_antisymm (lamD_le k b hb) hble |>.symm ▸ rfl

instance nonemptyJD (k : ℕ) : Nonempty {x : D k // JoinIrred (D k) x} :=
  ⟨⟨lamD k, joinIrred_lamD k⟩⟩

/-- **`EndP (D k)` is rigid, at every level.** -/
theorem endP_D_rigid (k : ℕ) [Fintype (EndP (D k))] :
    Subsingleton (EndP (D k) ≃o EndP (D k)) := by
  letI := realUniqueAtomCoatom k
  exact EndPRigid.endP_rigid (D_all_rigid k)

/-- **Uniqueness of the action at the tower, unconditionally.**

Over `D k` there is exactly one injective monotone tripointed action on
`D (k+1)`, and it is `Φ`'s.  No rigidity hypothesis: `endP_D_rigid` discharges
it at every level. -/
theorem phiTower_unique (k : ℕ) [Fintype (EndP (D k))]
    (f : TowerHom k k) (hf : Function.Injective f.toFun)
    (ψ : EndP (D k) →o EndP (D k)) (hψ : Function.Injective ψ) :
    phiTwist f ψ (hmk k) (hbtk k) = phiTower f :=
  phiTower_unique_of_rigid k (endP_D_rigid k) f hf ψ hψ

end Tower

end PhiTriTower
