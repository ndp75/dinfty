import Dinfty.AssemblyChain

open GluingTowerLibrary SierpinskiApplication

-- [D-2913] §tri-v2-in-Lean-the-tripointed-category
open scoped Classical

universe u

namespace PhiTri

-- [D-2914] §The-bottom-and-top-of-the-glued-object-over
section Bounds

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-2915] leGlueGen_tagA_bot
theorem leGlueGen_tagA_bot (m : P) (x : GlueBaseGen P) :
    leGlueGen m (Sum.inl (⊥ : P)) x := by
  refine ⟨Sum.inl (⊥ : P), self_mem_occsGen _ _, x, self_mem_occsGen _ _, ?_⟩
  cases x with
  | inl a => exact bot_le
  | inr x => cases x with
    | inl _ => exact bot_le
    | inr _ => trivial

-- [D-2916] leGlueGen_tagC_top
theorem leGlueGen_tagC_top (m : P) (x : GlueBaseGen P) :
    leGlueGen m x (Sum.inr (Sum.inr (⊤ : P))) := by
  refine ⟨x, self_mem_occsGen _ _, Sum.inr (Sum.inr (⊤ : P)), self_mem_occsGen _ _, ?_⟩
  cases x with
  | inl _ => trivial
  | inr x => cases x with
    | inl _ => exact le_top
    | inr _ => exact le_top

end Bounds

-- [D-2917] §The-tripointed-category
-- [D-2918] TriPointed
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

-- [D-2919] TriHom
structure TriHom (X Y : TriPointed) where
  toFun : X.carrier → Y.carrier
  monotone' : Monotone toFun
  map_bot : toFun ⊥ = ⊥
  map_mid : toFun X.mid = Y.mid
  map_top : toFun ⊤ = ⊤

-- [D-2920] inst-TriPointed
instance {X Y : TriPointed} : CoeFun (TriHom X Y) (fun _ => X.carrier → Y.carrier) :=
  ⟨TriHom.toFun⟩

-- [D-2921] TriHom.id
def TriHom.id (X : TriPointed) : TriHom X X where
  toFun := _root_.id
  monotone' := monotone_id
  map_bot := rfl
  map_mid := rfl
  map_top := rfl

-- [D-2922] TriHom.comp
def TriHom.comp {X Y Z : TriPointed} (g : TriHom Y Z) (f : TriHom X Y) : TriHom X Z where
  toFun := g.toFun ∘ f.toFun
  monotone' := g.monotone'.comp f.monotone'
  map_bot := by show g.toFun (f.toFun ⊥) = ⊥; rw [f.map_bot, g.map_bot]
  map_mid := by show g.toFun (f.toFun X.mid) = Z.mid; rw [f.map_mid, g.map_mid]
  map_top := by show g.toFun (f.toFun ⊤) = ⊤; rw [f.map_top, g.map_top]

-- [D-2923] §tri-v2-on-objects
-- [D-2924] §The-three-distinguished-points-of-the-glued
-- [D-2925] phiBot
def phiBot (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  ⟨Sum.inl (⊥ : X.carrier), rfl⟩

-- [D-2926] phiTop
def phiTop (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  ⟨Sum.inr (Sum.inr (⊤ : X.carrier)), by
    simp only [canonGen]
    rw [if_neg (Ne.symm X.bot_ne_top), if_neg (Ne.symm X.mid_ne_top)]⟩

-- [D-2927] phiMid
noncomputable def phiMid (X : TriPointed) : GlueCarGen (P := X.carrier) X.mid :=
  GenContinuity.tagBGen X.mid X.mid_ne_bot X.bot_ne_top X.mid

-- [D-2928] phiMid_val
theorem phiMid_val (X : TriPointed) :
    (phiMid X).val = Sum.inr (Sum.inl X.mid) :=
  GenContinuity.tagBGen_val_of_ne_bot X.mid X.mid_ne_bot X.bot_ne_top X.mid_ne_bot

-- [D-2929] phiMid_ne_phiBot
theorem phiMid_ne_phiBot (X : TriPointed) : phiMid X ≠ phiBot X := by
  intro h
  have hv : (phiMid X).val = (phiBot X).val := congrArg Subtype.val h
  rw [phiMid_val] at hv
  exact absurd hv (by simp [phiBot])

-- [D-2930] phiMid_ne_phiTop
theorem phiMid_ne_phiTop (X : TriPointed) : phiMid X ≠ phiTop X := by
  intro h
  have hv : (phiMid X).val = (phiTop X).val := congrArg Subtype.val h
  rw [phiMid_val] at hv
  exact absurd hv (by simp [phiTop])

-- [D-2931] phiBot_ne_phiTop
theorem phiBot_ne_phiTop (X : TriPointed) : phiBot X ≠ phiTop X := by
  intro h
  have hv : (phiBot X).val = (phiTop X).val := congrArg Subtype.val h
  exact absurd hv (by simp [phiBot, phiTop])

-- [D-2932] glueBoundedOrderGen
@[reducible] noncomputable def glueBoundedOrderGen (X : TriPointed) :
    letI := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
    BoundedOrder (GlueCarGen (P := X.carrier) X.mid) :=
  letI := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
  { top := phiTop X
    bot := phiBot X
    le_top := fun z => leGlueGen_tagC_top X.mid z.1
    bot_le := fun z => leGlueGen_tagA_bot X.mid z.1 }

-- [D-2933] Phi
noncomputable def Phi (X : TriPointed) : TriPointed where
  carrier := GlueCarGen (P := X.carrier) X.mid
  dec := Classical.decEq _
  order := glueCarPartialOrderGen X.mid X.mid_ne_bot X.mid_ne_top X.bot_ne_top
  bdd := glueBoundedOrderGen X
  mid := phiMid X
  mid_ne_bot := phiMid_ne_phiBot X
  mid_ne_top := phiMid_ne_phiTop X
  bot_ne_top := phiBot_ne_phiTop X

-- [D-2934] §tri-v2-on-morphisms-and-the-functor-laws
-- [D-2935] mapFun
def mapFun {X Y : TriPointed} (f : TriHom X Y) :
    GlueBaseGen X.carrier → GlueBaseGen Y.carrier :=
  GenContinuity.baseMapGen ⟨f.toFun, f.monotone'⟩

-- [D-2936] PreservesId
def PreservesId : Prop :=
  ∀ (X : TriPointed.{u}) (z : GlueBaseGen X.carrier), mapFun (TriHom.id X) z = z

-- [D-2937] PreservesComp
def PreservesComp : Prop :=
  ∀ (X Y Z : TriPointed.{u}) (g : TriHom Y Z) (f : TriHom X Y)
    (z : GlueBaseGen X.carrier),
    mapFun (TriHom.comp g f) z = mapFun g (mapFun f z)

-- [D-2938] §The-raw-tagwise-laws-true-but-NOT-ingredient-2
-- [D-2939] preservesId
theorem preservesId : PreservesId := by
  intro X z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

-- [D-2940] preservesComp
theorem preservesComp : PreservesComp := by
  intro X Y Z g f z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

-- [D-2941] §Ingredient-2-proper-the-action-on-the-glued
-- [D-2942] TriEmb
structure TriEmb (X Y : TriPointed) extends TriHom X Y where
  inj : Function.Injective toFun

-- [D-2943] TriEmb.hom
def TriEmb.hom {X Y : TriPointed} (f : TriEmb X Y) : X.carrier →o Y.carrier :=
  ⟨f.toFun, f.monotone'⟩

-- [D-2944] glueTwist_self
theorem glueTwist_self {P P' : Type u} [DecidableEq P] [PartialOrder P]
    [BoundedOrder P] [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
    (g : P →o P') : CopyBFreedom.glueTwist g g = GenContinuity.baseMapGen g := by
  funext z
  cases z with
  | inl _ => rfl
  | inr z => cases z with
    | inl _ => rfl
    | inr _ => rfl

-- [D-2945] Phi.map
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

-- [D-2946] §The-functor-laws-on-the-glued-object-ingredient
-- [D-2947] Phi.map_id
theorem Phi.map_id (X : TriPointed) (z : (Phi X).carrier) :
    (Phi.map ⟨TriHom.id X, fun _ _ h => h⟩).toFun z = z := by
  apply Subtype.ext
  show GenContinuity.baseMapGen (⟨_root_.id, monotone_id⟩ : X.carrier →o X.carrier) z.1 = z.1
  cases h : z.1 with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

-- [D-2948] Phi.map_comp
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
