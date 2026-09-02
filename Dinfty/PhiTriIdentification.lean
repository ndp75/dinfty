import Dinfty.PhiTriFunctor
import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

/-!
# The identification: when is a tripointed action `Φ`'s action?

`PhiTriFunctor` builds one morphism action, `phiFun f`.  Pillar A's remaining
half of ingredient 2 asks whether it is **the** action — whether `baseMapGen`
and `Φ_tri_v2`'s action coincide.  This file answers that in the form the
question actually has.

## The space of tripointed actions is exactly one map wide

`CopyBFreedom` showed the copy-`B` component of a `Gen`-layer action is free:
`glueTwist g ψ` is monotone and well-defined for **any** monotone `ψ` with
`ψ ⊤ = ⊤`, with no relation to `g` at all.  Descending that through `canonGen`
the way `phiFun` does gives `phiTwist f ψ`, and:

* `phiTwist_monotone`, `phiTwist_triBot/triMark/triTop` — every `phiTwist f ψ`
  really is a monotone tripointed action lying over `f`;
* `phiTwist_self` — `phiTwist f f.toFun = phiFun f`, so `Φ`'s action is the
  `ψ = f` point of that family.

So the family of candidate actions over `f` is parametrised by `ψ`, and the
identification is *precisely* the question of which `ψ`.

## The criterion, and it is an iff

```lean
phiTwist_eq_phiFun_iff : phiTwist f ψ = phiFun f  ↔  ∀ b ≠ ⊥, ψ b = f.toFun b
```

Nothing is hidden in the other two copies: they agree by construction, and the
glued order provides **no coupling** between copy `B`'s interior and the rest
(that is `CopyBFreedom`'s content, and one can read it off the nine tag-pairs —
every mixed pair is mediated by `m`, and `f m = m'` carries all of them).  So
the identification is a copy-`B` question and cannot be made anything else.

## What closes it

`MonotoneInjectionRigid.eq_id_of_rigid`: on a **rigid finite** poset the only
monotone injection is the identity.  So at a rigid base an injective `ψ` is
forced to be `id` — and so is `f.toFun` — and the criterion is met:

```lean
phiTwist_eq_phiFun_of_rigid : Subsingleton (P ≃o P) → Injective f.toFun →
    Injective ψ → phiTwist f ψ = phiFun f
```

The same hypothesis collapses the tripointed endomorphism monoid itself
(`triHom_toFun_eq_id`), which is why the identification is *available* at a rigid
base rather than merely plausible.

## Scope — say it precisely

This is the `Gen` layer, and the closure is **conditional on base rigidity**.
For the tower, level `k+1`'s glue base is `EndP (D k)`:

* `k = 0` — `EndP (Fin 3)` rigid, by enumeration
  (`_archive/check_endp_D0_automorphisms.py`);
* `k = 1` — `EndP (D 1)` rigid, by `Dinfty/JoinIrredRigidity.lean` plus the
  432-element computation (`_archive/check_endp_D1_rigidity_threshold.py`);
* `k ≥ 2` — open, and it is CONJ′ (`_archive/check_threshold_preservation_uniform.py`),
  not another level of computation.

Without rigidity the identification is **false**, not merely unproved:
`CopyBFreedom.swapTwist_ne_baseMapGen` exhibits an injective monotone twist on
the four-element diamond.  So "the identification holds" is a statement about
the base, and this file is the theorem that says which statement.
-/

open scoped Classical

universe u

namespace PhiTriIdentification

open PhiTriFunctor GenContinuity CopyBFreedom

section Twist

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

/-- **The general tripointed action over `f`**: `f` on copies `A` and `C`, an
arbitrary monotone `ψ` on copy `B`, descended through `canonGen` exactly as
`phiFun` is. -/
def phiTwist (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    GlueCarGen (P := P) m → GlueCarGen (P := P') m' :=
  fun x => ⟨canonGen m' (glueTwist f.toFun ψ x.1), canonGen_idem m' hm' hbt' _⟩

@[simp] theorem phiTwist_val (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) (x : GlueCarGen (P := P) m) :
    (phiTwist f ψ hm' hbt' x).1 = canonGen m' (glueTwist f.toFun ψ x.1) := rfl

/-- Twisting by `g` itself is not twisting at all. -/
theorem glueTwist_self (g : P →o P') : glueTwist g g = baseMapGen g := by
  funext x
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl b => rfl
    | inr c => rfl

/-- **`Φ`'s action is the `ψ = f` point of the family.** -/
theorem phiTwist_self (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f f.toFun hm' hbt' = phiFun f hm' hbt' := by
  funext x
  refine Subtype.ext ?_
  show canonGen m' (glueTwist f.toFun f.toFun x.1)
    = canonGen m' (baseMapGen f.toFun x.1)
  rw [glueTwist_self]

/-! ### Every `phiTwist` is a monotone tripointed action -/

theorem phiTwist_monotone (f : TriHom m m') (ψ : P →o P') (hψt : ψ ⊤ = ⊤)
    (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) {x y : GlueCarGen (P := P) m} (h : x ≤ y) :
    phiTwist f ψ hm' hbt' x ≤ phiTwist f ψ hm' hbt' y :=
  leGlueGen_canon m' hm' hmt' hbt'
    (glueTwist_monotone m m' hm hm' hbt f.toFun ψ f.map_mark hψt x.2 y.2 h)

theorem phiTwist_triBot (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triBot m) = triBot m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun ⊥)) = Sum.inl ⊥
  rw [f.map_bot]
  rfl

theorem phiTwist_triMark (f : TriHom m m') (ψ : P →o P') (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triMark m) = triMark m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun m)) = Sum.inl m'
  rw [f.map_mark]
  rfl

theorem phiTwist_triTop (f : TriHom m m') (ψ : P →o P') (hmt : m ≠ ⊤)
    (hbt : (⊥ : P) ≠ ⊤) (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤) :
    phiTwist f ψ hm' hbt' (triTop m hmt hbt) = triTop m' hmt' hbt' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inr (Sum.inr (f.toFun ⊤))) = Sum.inr (Sum.inr ⊤)
  rw [f.map_top]
  simp [canonGen, Ne.symm hbt', Ne.symm hmt']

/-! ### The criterion -/

/-- **The identification is exactly a copy-`B` question.**

Copies `A` and `C` agree by construction, and the glued order does not couple
copy `B`'s interior to them, so the whole content of "is this `Φ`'s action?" is
"does its copy-`B` component agree with `f`?". -/
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

/-! ## What closes the identification -/

section Rigid

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P] [Finite P]
variable {m : P}

/-- At a rigid finite base the tripointed endomorphism monoid is trivial: an
injective tripointed self-map is the identity. -/
theorem triHom_toFun_eq_id (hrigid : Subsingleton (P ≃o P)) (f : TriHom m m)
    (hf : Function.Injective f.toFun) : (f.toFun : P → P) = id :=
  MonotoneInjectionRigid.eq_id_of_rigid hrigid f.toFun.monotone hf

/-- **The identification, at a rigid base.**

An injective copy-`B` component over a rigid finite base is forced to be the
identity, and so is `f`; the criterion is then met and the action is `Φ`'s.

Without rigidity this is *false*, not merely unproved —
`CopyBFreedom.swapTwist_ne_baseMapGen` twists the four-element diamond by
`Prod.swap`. -/
theorem phiTwist_eq_phiFun_of_rigid (hrigid : Subsingleton (P ≃o P))
    (f : TriHom m m) (hf : Function.Injective f.toFun)
    (ψ : P →o P) (hψ : Function.Injective ψ) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    phiTwist f ψ hm hbt = phiFun f hm hbt := by
  refine (phiTwist_eq_phiFun_iff f ψ hm hbt).mpr (fun b _ => ?_)
  have h1 : (ψ : P → P) = id :=
    MonotoneInjectionRigid.eq_id_of_rigid hrigid ψ.monotone hψ
  have h2 : (f.toFun : P → P) = id := triHom_toFun_eq_id hrigid f hf
  rw [congrFun h1 b, congrFun h2 b]

/-- The identification in its bluntest form: over a rigid finite base there is
only **one** injective monotone tripointed action at all, and it is `Φ`'s. -/
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
