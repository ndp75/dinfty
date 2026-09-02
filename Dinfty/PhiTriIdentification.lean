import Dinfty.PhiTriFunctor
import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

-- [D-2056] §The-identification-when-is-a-tripointed-action-s
open scoped Classical

universe u

namespace PhiTriIdentification

open PhiTriFunctor GenContinuity CopyBFreedom

section Twist

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

-- [D-2057] phiTwist
def phiTwist (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    GlueCarGen (P := P) m → GlueCarGen (P := P') m' :=
  fun x => ⟨canonGen m' (glueTwist f.toFun ψ x.1), canonGen_idem m' hm' hbt' _⟩

-- [D-2058] phiTwist_val
@[simp] theorem phiTwist_val (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) (x : GlueCarGen (P := P) m) :
    (phiTwist f ψ hm' hbt' x).1 = canonGen m' (glueTwist f.toFun ψ x.1) := rfl

-- [D-2059] glueTwist_self
theorem glueTwist_self (g : P →o P') : glueTwist g g = baseMapGen g := by
  funext x
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl b => rfl
    | inr c => rfl

-- [D-2060] phiTwist_self
theorem phiTwist_self (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f f.toFun hm' hbt' = phiFun f hm' hbt' := by
  funext x
  refine Subtype.ext ?_
  show canonGen m' (glueTwist f.toFun f.toFun x.1)
    = canonGen m' (baseMapGen f.toFun x.1)
  rw [glueTwist_self]

-- [D-2061] §Every-phiTwist-is-a-monotone-tripointed-action
-- [D-2062] phiTwist_monotone
theorem phiTwist_monotone (f : TriHom m m') (ψ : P →o P') (hψt : ψ ⊤ = ⊤)
    (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) {x y : GlueCarGen (P := P) m} (h : x ≤ y) :
    phiTwist f ψ hm' hbt' x ≤ phiTwist f ψ hm' hbt' y :=
  leGlueGen_canon m' hm' hmt' hbt'
    (glueTwist_monotone m m' hm hm' hbt f.toFun ψ f.map_mark hψt x.2 y.2 h)

-- [D-2063] phiTwist_triBot
theorem phiTwist_triBot (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triBot m) = triBot m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun ⊥)) = Sum.inl ⊥
  rw [f.map_bot]
  rfl

-- [D-2064] phiTwist_triMark
theorem phiTwist_triMark (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triMark m) = triMark m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun m)) = Sum.inl m'
  rw [f.map_mark]
  rfl

-- [D-2065] phiTwist_triTop
theorem phiTwist_triTop (f : TriHom m m') (ψ : P →o P') (hmt : m ≠ ⊤)
    (hbt : (⊥ : P) ≠ ⊤) (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triTop m hmt hbt) = triTop m' hmt' hbt' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inr (Sum.inr (f.toFun ⊤))) = Sum.inr (Sum.inr ⊤)
  rw [f.map_top]
  simp [canonGen, Ne.symm hbt', Ne.symm hmt']

-- [D-2066] §The-criterion
-- [D-2067] phiTwist_eq_phiFun_iff
theorem phiTwist_eq_phiFun_iff (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' = phiFun f hm' hbt'
      ↔ ∀ b : P, b ≠ ⊥ → ψ b = f.toFun b := by
  constructor
  · intro h b hb
    have hcan : canonGen m (Sum.inr (Sum.inl b)) = Sum.inr (Sum.inl b) := by
      simp [canonGen, hb]
    have := congrArg Subtype.val
      (congrFun h (⟨Sum.inr (Sum.inl b), hcan⟩ : GlueCarGen (P := P) m))
    simp only [phiTwist_val, phiFun_val] at this
    show ψ b = f.toFun b
    by_cases h1 : ψ b = ⊥
    · by_cases h2 : f.toFun b = ⊥
      · rw [h1, h2]
      · rw [show glueTwist f.toFun ψ (Sum.inr (Sum.inl b))
              = Sum.inr (Sum.inl (ψ b)) from rfl,
            show baseMapGen f.toFun (Sum.inr (Sum.inl b))
              = Sum.inr (Sum.inl (f.toFun b)) from rfl] at this
        simp [canonGen, h1, h2] at this
    · rw [show glueTwist f.toFun ψ (Sum.inr (Sum.inl b))
            = Sum.inr (Sum.inl (ψ b)) from rfl,
          show baseMapGen f.toFun (Sum.inr (Sum.inl b))
            = Sum.inr (Sum.inl (f.toFun b)) from rfl] at this
      by_cases h2 : f.toFun b = ⊥
      · simp [canonGen, h1, h2] at this
      · simpa [canonGen, h1, h2] using this
  · intro h
    funext x
    refine Subtype.ext ?_
    show canonGen m' (glueTwist f.toFun ψ x.1)
      = canonGen m' (baseMapGen f.toFun x.1)
    obtain ⟨v, hv⟩ := x
    cases v with
    | inl a => rfl
    | inr y => cases y with
      | inl b =>
          have hb : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hv
          show canonGen m' (Sum.inr (Sum.inl (ψ b)))
            = canonGen m' (Sum.inr (Sum.inl (f.toFun b)))
          rw [h b hb]
      | inr c => rfl

end Twist

-- [D-2068] §What-closes-the-identification
section Rigid

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P] [Finite P]
variable {m : P}

-- [D-2069] triHom_toFun_eq_id
theorem triHom_toFun_eq_id (hrigid : Subsingleton (P ≃o P)) (f : TriHom m m)
    (hf : Function.Injective f.toFun) : (f.toFun : P → P) = id :=
  MonotoneInjectionRigid.eq_id_of_rigid hrigid f.toFun.monotone hf

-- [D-2070] phiTwist_eq_phiFun_of_rigid
theorem phiTwist_eq_phiFun_of_rigid (hrigid : Subsingleton (P ≃o P))
    (f : TriHom m m) (hf : Function.Injective f.toFun)
    (ψ : P →o P) (hψ : Function.Injective ψ) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    phiTwist f ψ hm hbt = phiFun f hm hbt := by
  refine (phiTwist_eq_phiFun_iff f ψ hm hbt).mpr (fun b _ => ?_)
  have h1 : (ψ : P → P) = id :=
    MonotoneInjectionRigid.eq_id_of_rigid hrigid ψ.monotone hψ
  have h2 : (f.toFun : P → P) = id := triHom_toFun_eq_id hrigid f hf
  rw [congrFun h1 b, congrFun h2 b]

-- [D-2071] phiTwist_eq_phiFun_id
theorem phiTwist_eq_phiFun_id (hrigid : Subsingleton (P ≃o P))
    (f : TriHom m m) (hf : Function.Injective f.toFun)
    (ψ : P →o P) (hψ : Function.Injective ψ) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    phiTwist f ψ hm hbt = _root_.id := by
  rw [phiTwist_eq_phiFun_of_rigid hrigid f hf ψ hψ hm hbt]
  have hf' : f = TriHom.id m := by
    obtain ⟨g, hb, hmk, ht⟩ := f
    have : g = OrderHom.id := OrderHom.ext _ _ (triHom_toFun_eq_id hrigid ⟨g, hb, hmk, ht⟩ hf)
    subst this
    rfl
  rw [hf']
  exact phiFun_id m hm hbt

end Rigid

end PhiTriIdentification
