import Dinfty.AssemblyChain

open GluingTowerLibrary SierpinskiApplication

/-!
# `Φ_tri_v2` in Lean — the tripointed category, and `Φ` as an endofunctor on it

Pillar A's open item — that `GenContinuity.baseMapGen` and `Φ_tri_v2`'s morphism
action agree — was found (2026-08-28) to be *inexpressible*: `Φ_tri_v2` had no
Lean definition at all, existing only in the vault's prose.  This module is that
prerequisite.

## What `Φ_tri_v2` is, from the vault

`Results/03 Phi Gluing Functor.md`: it matches Ratnayake et al. 2021 §2.2
exactly — three copies `a`, `b`, `c` glued along

    a.L ~ b.T,   a.R ~ c.T,   b.R ~ c.L

with new distinguished points `T' = a.T`, `L' = b.L`, `R' = c.R`.

**The Lean library already has this as its object action.**  `canonGen`'s three
redirects are precisely those three seams:

| Ratnayake | `canonGen` |
|---|---|
| `a.L ~ b.T` | `tag_B ⊥ ↦ tag_A m` |
| `a.R ~ c.T` | `tag_C ⊥ ↦ tag_A ⊤` |
| `b.R ~ c.L` | `tag_C m ↦ tag_B ⊤` |

with `(T, L, R) = (⊥, m, ⊤)`.  So `Φ_tri_v2` on objects **is** `GlueCarGen`, and
what was missing is not the construction but the *category it is a functor on*:
the tripointed objects and tripointed maps.  This module supplies those.

## The marked point is `const_L`, not `id`

Load-bearing, and the source of a long-lived error.  `Φ_tri_v2` is applied to
`H = [X→X]`, whose three distinguished points are `(const_T, const_L, const_R)`
— **all three constants**.  An early reading took the middle one to be `id`; that
was a 2-chain artefact, where `[X→X]` has three elements and `id` *is* the middle
one, so `id` and `const_L` coincide.  At the real 3-chain base
`H₀ = EndP(chain 3)` has ten elements and `m = const_L = (1,1,1) ≠ id = (0,1,2)`
(Finding file Update 22; `Results/03` lines 63–64).

`TriPointed` therefore takes the marked point as *data*, and the `End` functor
below marks `[X→X]` at `constHom X.mid` — a constant — never at `OrderHom.id`.

## What this module does and does not give

**Defines:** `TriPointed` (objects), `TriHom` (tripointed maps), the bottom and
top of `GlueCarGen` over an arbitrary base (ported from the finite layer, where
neither needed finiteness), `PhiTri.Phi` (the object action), and `PhiTri.mapFun` (the
morphism action, which is `baseMapGen`).

**Does not prove:** the functor laws.  `PhiTri.PreservesId` and
`PhiTri.PreservesComp` are stated as `Prop`s — they are *ingredient 2*, still
open, and this module deliberately does not attempt them.  What it buys is that
ingredient 2 and the pillar-A identification are now **statable**, which they
were not this morning.
-/

open scoped Classical

universe u

namespace PhiTri

/-! ## The bottom and top of the glued object, over an arbitrary base

Both ported from the finite `GlueCar` layer; neither proof used finiteness. -/

section Bounds

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- `tag_A ⊥` is below everything: copy `A` by `⊥ ≤ a`, copy `B` by `⊥ ≤ m`,
copy `C` unconditionally. -/
theorem leGlueGen_tagA_bot (m : P) (x : GlueBaseGen P) :
    leGlueGen m (Sum.inl (⊥ : P)) x := by
  refine ⟨Sum.inl (⊥ : P), self_mem_occsGen _ _, x, self_mem_occsGen _ _, ?_⟩
  cases x with
  | inl a => exact bot_le
  | inr x => cases x with
    | inl _ => exact bot_le
    | inr _ => trivial

/-- `tag_C ⊤` is above everything: copy `A` unconditionally, copy `B` by
`m ≤ ⊤`, copy `C` by `c ≤ ⊤`. -/
theorem leGlueGen_tagC_top (m : P) (x : GlueBaseGen P) :
    leGlueGen m x (Sum.inr (Sum.inr (⊤ : P))) := by
  refine ⟨x, self_mem_occsGen _ _, Sum.inr (Sum.inr (⊤ : P)), self_mem_occsGen _ _, ?_⟩
  cases x with
  | inl _ => trivial
  | inr x => cases x with
    | inl _ => exact le_top
    | inr _ => exact le_top

end Bounds

/-! ## The tripointed category -/

/-- A **tripointed object**: a decidable bounded poset with a distinguished
interior point.  `(T, L, R) = (⊥, mid, ⊤)` in Ratnayake's notation.

The nondegeneracy fields are exactly the side conditions the glue construction
takes throughout the library (`hm`, `hmt`, `hbt`). -/
structure TriPointed : Type (u + 1) where
  carrier : Type u
  dec : DecidableEq carrier
  order : PartialOrder carrier
  bdd : BoundedOrder carrier
  mid : carrier
  mid_ne_bot : mid ≠ ⊥
  mid_ne_top : mid ≠ ⊤
  bot_ne_top : (⊥ : carrier) ≠ ⊤

attribute [instance] TriPointed.dec TriPointed.order TriPointed.bdd

/-- A **tripointed map**: monotone, and preserving all three distinguished
points.  This is the `Hom_tri` the vault's functoriality and local-continuity
proofs are stated over. -/
structure TriHom (X Y : TriPointed) where
  toFun : X.carrier → Y.carrier
  monotone' : Monotone toFun
  map_bot : toFun ⊥ = ⊥
  map_mid : toFun X.mid = Y.mid
  map_top : toFun ⊤ = ⊤

instance {X Y : TriPointed} : CoeFun (TriHom X Y) (fun _ => X.carrier → Y.carrier) :=
  ⟨TriHom.toFun⟩

/-- The identity tripointed map. -/
def TriHom.id (X : TriPointed) : TriHom X X where
  toFun := _root_.id
  monotone' := monotone_id
  map_bot := rfl
  map_mid := rfl
  map_top := rfl

/-- Composition of tripointed maps. -/
def TriHom.comp {X Y Z : TriPointed} (g : TriHom Y Z) (f : TriHom X Y) : TriHom X Z where
  toFun := g.toFun ∘ f.toFun
  monotone' := g.monotone'.comp f.monotone'
  map_bot := by show g.toFun (f.toFun ⊥) = ⊥; rw [f.map_bot, g.map_bot]
  map_mid := by show g.toFun (f.toFun X.mid) = Z.mid; rw [f.map_mid, g.map_mid]
  map_top := by show g.toFun (f.toFun ⊤) = ⊤; rw [f.map_top, g.map_top]

/-! ## `Φ_tri_v2` on objects -/

/-! ### The three distinguished points of the glued object

Named separately so their distinctness can be proved before the `BoundedOrder`
instance is assembled — `T' = a.T`, `L' = b.L`, `R' = c.R` in Ratnayake's
notation. -/

/-- `T' = a.T = tag_A ⊥`. -/
def phiBot (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  ⟨Sum.inl (⊥ : X.carrier), rfl⟩

/-- `R' = c.R = tag_C ⊤`. -/
def phiTop (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  ⟨Sum.inr (Sum.inr (⊤ : X.carrier)), by
    simp only [canonGen]
    rw [if_neg (Ne.symm X.bot_ne_top), if_neg (Ne.symm X.mid_ne_top)]⟩

/-- `L' = b.L = tag_B mid` — the new marked point. -/
noncomputable def phiMid (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  GenContinuity.tagBGen X.mid X.mid_ne_bot X.bot_ne_top X.mid

theorem phiMid_val (X : TriPointed) :
    (phiMid X).val = Sum.inr (Sum.inl X.mid) :=
  GenContinuity.tagBGen_val_of_ne_bot X.mid X.mid_ne_bot X.bot_ne_top X.mid_ne_bot

theorem phiMid_ne_phiBot (X : TriPointed) : phiMid X ≠ phiBot X := by
  intro h
  have hv : (phiMid X).val = (phiBot X).val := congrArg Subtype.val h
  rw [phiMid_val] at hv
  exact absurd hv (by simp [phiBot])

theorem phiMid_ne_phiTop (X : TriPointed) : phiMid X ≠ phiTop X := by
  intro h
  have hv : (phiMid X).val = (phiTop X).val := congrArg Subtype.val h
  rw [phiMid_val] at hv
  exact absurd hv (by simp [phiTop])

theorem phiBot_ne_phiTop (X : TriPointed) : phiBot X ≠ phiTop X := by
  intro h
  have hv : (phiBot X).val = (phiTop X).val := congrArg Subtype.val h
  exact absurd hv (by simp [phiBot, phiTop])

/-- The glued carrier is bounded, over an arbitrary base. -/
@[reducible] noncomputable def glueBoundedOrderGen (X : TriPointed) :
    letI := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
    BoundedOrder (GlueCarGen (P := X.carrier) X.mid) :=
  letI := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
  { top := phiTop X
    bot := phiBot X
    le_top := fun z => leGlueGen_tagC_top X.mid z.1
    bot_le := fun z => leGlueGen_tagA_bot X.mid z.1 }

/-- **`Φ_tri_v2` on objects.**  Three copies glued at Ratnayake's three seams —
which is exactly what `canonGen` does — with the new distinguished point
`L' = b.L = tag_B mid`. -/
noncomputable def Phi (X : TriPointed) : TriPointed where
  carrier := GlueCarGen (P := X.carrier) X.mid
  dec := Classical.decEq _
  order := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
  bdd := glueBoundedOrderGen X
  mid := phiMid X
  mid_ne_bot := phiMid_ne_phiBot X
  mid_ne_top := phiMid_ne_phiTop X
  bot_ne_top := phiBot_ne_phiTop X

/-! ## `Φ_tri_v2` on morphisms, and the functor laws

The morphism action is `baseMapGen` — the map pillar A's identification is about.
Its well-definedness on the glued carrier is `NormalizedGlueMap`'s content; the
`Prop`s below are **ingredient 2**, and are deliberately not proved here. -/

/-- The underlying map of `Φ_tri_v2` on a tripointed morphism: `baseMapGen`,
tagwise. -/
def mapFun {X Y : TriPointed} (f : TriHom X Y) :
    GlueBaseGen X.carrier → GlueBaseGen Y.carrier :=
  GenContinuity.baseMapGen ⟨f.toFun, f.monotone'⟩

/-- **Ingredient 2, first law (F1).**  `Φ_tri_v2` preserves identities. -/
def PreservesId : Prop :=
  ∀ (X : TriPointed.{u}) (z : GlueBaseGen X.carrier), mapFun (TriHom.id X) z = z

/-- **Ingredient 2, second law (F2).**  `Φ_tri_v2` preserves composition. -/
def PreservesComp : Prop :=
  ∀ (X Y Z : TriPointed.{u}) (g : TriHom Y Z) (f : TriHom X Y)
    (z : GlueBaseGen X.carrier),
    mapFun (TriHom.comp g f) z = mapFun g (mapFun f z)


/-! ## The raw tagwise laws — true, but NOT ingredient 2

`PreservesId`/`PreservesComp` as stated above are about the **raw**
`GlueBaseGen`, where `baseMapGen` is tagwise and both laws are immediate.  They
are proved here for completeness, and then set aside: **ingredient 2 is the
functor law for the action on the *glued object* `GlueCarGen`**, which is a
different and harder statement because the action must first be shown to
*descend* — to carry canon-fixed points to canon-fixed points.  Stating the easy
version and calling it ingredient 2 would be exactly the finite/limit-style
conflation this project keeps logging. -/

theorem preservesId : PreservesId := by
  intro X z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

theorem preservesComp : PreservesComp := by
  intro X Y Z g f z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

/-! ## Ingredient 2 proper: the action on the glued object

Descent needs **injectivity** — the copy-`C` branch of `canonGen` must send
`c ≠ ⊥, c ≠ m` to `g c ≠ ⊥, g c ≠ m'`, which tripointedness alone does not give.
That is why the vault's category is one of *embeddings*. -/

/-- A tripointed **embedding**: a tripointed map that is injective. -/
structure TriEmb (X Y : TriPointed) extends TriHom X Y where
  inj : Function.Injective toFun

/-- The bundled monotone map underlying a tripointed embedding. -/
def TriEmb.hom {X Y : TriPointed} (f : TriEmb X Y) : X.carrier →o Y.carrier :=
  ⟨f.toFun, f.monotone'⟩

/-- `glueTwist` at `ψ = g` is exactly `baseMapGen g`, so `CopyBFreedom`'s
descent and monotonicity lemmas apply to the morphism action directly. -/
theorem glueTwist_self {P P' : Type u} [DecidableEq P] [PartialOrder P]
    [BoundedOrder P] [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
    (g : P →o P') : CopyBFreedom.glueTwist g g = GenContinuity.baseMapGen g := by
  funext z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

/-- **`Φ_tri_v2` on morphisms.**  The action descends to the glued object and is
again a tripointed embedding.

Every component reuses a lemma proved earlier today: descent from
`CopyBFreedom.glueTwist_canonGen_fixed`, monotonicity from
`CopyBFreedom.glueTwist_monotone`, injectivity from
`CopyBFreedom.glueTwist_injective` — each specialised at `ψ = g` via
`glueTwist_self`. -/
noncomputable def Phi.map {X Y : TriPointed} (f : TriEmb X Y) :
    TriEmb (Phi X) (Phi Y) where
  toFun := fun z => ⟨GenContinuity.baseMapGen f.hom z.1, by
    rw [← glueTwist_self]
    exact CopyBFreedom.glueTwist_canonGen_fixed X.mid Y.mid f.hom f.hom
      f.map_bot f.map_mid f.inj
      (fun b hb hcon => hb (f.inj (show f.toFun b = f.toFun ⊥ by
        rw [f.map_bot]; exact hcon))) z.2⟩
  monotone' := by
    intro a b hab
    show leGlueGen Y.mid (GenContinuity.baseMapGen f.hom a.1)
      (GenContinuity.baseMapGen f.hom b.1)
    rw [← glueTwist_self]
    exact CopyBFreedom.glueTwist_monotone X.mid Y.mid X.mid_ne_bot Y.mid_ne_bot
      X.bot_ne_top f.hom f.hom f.map_mid f.map_top a.2 b.2 hab
  map_bot := by
    apply Subtype.ext
    show GenContinuity.baseMapGen f.hom (Sum.inl (⊥ : X.carrier))
      = Sum.inl (⊥ : Y.carrier)
    show Sum.inl (f.toFun ⊥) = Sum.inl (⊥ : Y.carrier)
    rw [f.map_bot]
  map_mid := by
    apply Subtype.ext
    show GenContinuity.baseMapGen f.hom (phiMid X).1 = (phiMid Y).1
    rw [phiMid_val, phiMid_val]
    show Sum.inr (Sum.inl (f.toFun X.mid)) = Sum.inr (Sum.inl Y.mid)
    rw [f.map_mid]
  map_top := by
    apply Subtype.ext
    show GenContinuity.baseMapGen f.hom (Sum.inr (Sum.inr (⊤ : X.carrier)))
      = Sum.inr (Sum.inr (⊤ : Y.carrier))
    show Sum.inr (Sum.inr (f.toFun ⊤)) = Sum.inr (Sum.inr (⊤ : Y.carrier))
    rw [f.map_top]
  inj := by
    intro a b hab
    apply Subtype.ext
    have hv : GenContinuity.baseMapGen f.hom a.1 = GenContinuity.baseMapGen f.hom b.1 :=
      congrArg Subtype.val hab
    rw [← glueTwist_self] at hv
    exact CopyBFreedom.glueTwist_injective f.hom f.hom f.inj f.inj hv

/-! ### The functor laws on the glued object — ingredient 2 -/

/-- **F1.**  `Φ_tri_v2` preserves identities, on the glued object. -/
theorem Phi.map_id (X : TriPointed) (z : (Phi X).carrier) :
    (Phi.map ⟨TriHom.id X, fun _ _ h => h⟩).toFun z = z := by
  apply Subtype.ext
  show GenContinuity.baseMapGen (⟨_root_.id, monotone_id⟩ : X.carrier →o X.carrier) z.1 = z.1
  cases h : z.1 with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

/-- **F2.**  `Φ_tri_v2` preserves composition, on the glued object. -/
theorem Phi.map_comp {X Y Z : TriPointed} (g : TriEmb Y Z) (f : TriEmb X Y)
    (z : (Phi X).carrier) :
    (Phi.map ⟨TriHom.comp g.toTriHom f.toTriHom, g.inj.comp f.inj⟩).toFun z
      = (Phi.map g).toFun ((Phi.map f).toFun z) := by
  apply Subtype.ext
  obtain ⟨zv, hzv⟩ := z
  cases zv with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

end PhiTri
