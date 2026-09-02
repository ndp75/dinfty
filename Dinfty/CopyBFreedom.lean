import Dinfty.BaseMapGenRigidity

open GluingTowerLibrary SierpinskiApplication

/-!
# The copy-`B` component is unconstrained — and the freedom is not a collapse

`BaseMapGenRigidity.collapseB` exhibits *one* map that agrees with `baseMapGen g`
on copies `A` and `C` and differs on copy `B`, by sending all of copy `B` to the
seam `tag_B ⊤`.  That reads like a degeneracy — a constant, a collapse — and
invites the guess that the freedom is somehow about deflating.

**It is not.**  The copy-`B` component of such a map is *arbitrary*:
`glueTwist g ψ` works for **any** monotone `ψ` with `ψ ⊤ = ⊤` (and `ψ` nonzero
on the canon-fixed region), with **no relation to `g` whatsoever**.

## Why the constraint is empty

Copy `A` reaches copy `B` only through `a ≤ m`, and copy `B` reaches copy `C`
only through `m ≤ c'`.  Both conditions are about `m`, and both are carried by
`g m = m'` alone — neither mentions the copy-`B` value.  Copy `B` is never below
copy `A`; copy `C` is below copy `B` only at `tag_B ⊤`, where `ψ ⊤ = ⊤` pins it.
Within copy `B` the order is `P`'s own, so monotonicity of `ψ` is all that is
asked.

So the glued order simply does not couple copy `B`'s interior to the other two
copies at all, beyond the two seams — and the seams are exactly where `ψ ⊥ = ⊥`
and `ψ ⊤ = ⊤` are forced.

## What this settles

`collapseB` is the instance `ψ = constant ⊤`, and its non-injectivity was the
one thing keeping Update 42's question open: does requiring an *injective*
action restore rigidity?  **No.**  `glueTwist_injective` shows `glueTwist g ψ`
is injective whenever `g` and `ψ` are, and `swapTwist_ne_baseMapGen` exhibits
this concretely on the four-element diamond `Fin 2 × Fin 2` with `ψ = Prod.swap`
— an order automorphism fixing `⊥` and `⊤`, so the resulting action is injective,
monotone, canon-preserving, agrees with `baseMapGen id` on copies `A` and `C`,
and still differs on copy `B`.

So: not a collapse, not a deflation, not a blowup — the copy-`B` component is
free, and injectivity does not constrain it.  An identification of `baseMapGen`
with `Φ_tri_v2`'s action must therefore compare the copy-`B` components
*directly*; no amount of structure on the other two copies, and no regularity
hypothesis on the map itself, will do it.

**Caveat on scope.**  This is a statement about arbitrary bases `P`.  Whether
the *tower's* levels `D k` admit a nontrivial `⊥`/`⊤`-fixing monotone injection
is a separate, concrete question, not answered here — though `D k` for `k ≥ 1`
is a 27-element non-chain lattice, so the expectation is that they do.
-/

open scoped Classical

universe u

namespace CopyBFreedom

open GenContinuity EndLocalContinuity BaseMapGenRigidity

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

/-- `baseMapGen g` on copies `A` and `C`; an arbitrary monotone `ψ` on copy `B`. -/
def glueTwist (g ψ : P →o P') : GlueBaseGen P → GlueBaseGen P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (ψ x))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

@[simp] theorem glueTwist_inl (g ψ : P →o P') (a : P) :
    glueTwist g ψ (Sum.inl a) = Sum.inl (g a) := rfl

@[simp] theorem glueTwist_inr_inl (g ψ : P →o P') (b : P) :
    glueTwist g ψ (Sum.inr (Sum.inl b)) = Sum.inr (Sum.inl (ψ b)) := rfl

@[simp] theorem glueTwist_inr_inr (g ψ : P →o P') (c : P) :
    glueTwist g ψ (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr (g c)) := rfl

theorem glueTwist_eq_on_tagA (g ψ : P →o P') (a : P) :
    glueTwist g ψ (Sum.inl a) = baseMapGen g (Sum.inl a) := rfl

theorem glueTwist_eq_on_tagC (g ψ : P →o P') (c : P) :
    glueTwist g ψ (Sum.inr (Sum.inr c)) = baseMapGen g (Sum.inr (Sum.inr c)) := rfl

/-- Well-defined on the canon-fixed region. -/
theorem glueTwist_canonGen_fixed (m : P) (m' : P') (g ψ : P →o P')
    (hgb : g ⊥ = ⊥) (hgm : g m = m') (hginj : Function.Injective g)
    (hpsib : ∀ b : P, b ≠ ⊥ → ψ b ≠ ⊥)
    {x : GlueBaseGen P} (hx : canonGen m x = x) :
    canonGen m' (glueTwist g ψ x) = glueTwist g ψ x := by
  cases x with
  | inl a => rfl
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      show canonGen m' (Sum.inr (Sum.inl (ψ b))) = Sum.inr (Sum.inl (ψ b))
      simp only [canonGen]; rw [if_neg (hpsib b hbne)]
    | inr c =>
      have hcb : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      have hcm : c ≠ m := by
        intro hcon
        have hval : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inl (⊤ : P)) := by
          simp only [canonGen]; rw [if_neg hcb, if_pos hcon]
        rw [hx] at hval
        exact absurd hval (by simp)
      show canonGen m' (Sum.inr (Sum.inr (g c))) = Sum.inr (Sum.inr (g c))
      simp only [canonGen]
      rw [if_neg (fun h => hcb (hginj (h.trans hgb.symm))),
          if_neg (fun h => hcm (hginj (h.trans hgm.symm)))]

/-- **Monotone for the glued order, for an arbitrary monotone `ψ`.**  The only
couplings between copy `B` and the rest are through `m`, and `g m = m'` carries
both; `ψ ⊤ = ⊤` pins the one seam where copy `C` sits below copy `B`. -/
theorem glueTwist_monotone (m : P) (m' : P') (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt : (⊥ : P) ≠ ⊤) (g ψ : P →o P') (hgm : g m = m') (hpsit : ψ ⊤ = ⊤)
    {x y : GlueBaseGen P}
    (hx : canonGen m x = x) (hy : canonGen m y = y)
    (h : leGlueGen m x y) :
    leGlueGen m' (glueTwist g ψ x) (glueTwist g ψ y) := by
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      have hle : a ≤ a' := (leGlueGen_tagA_tagA_iff m hm a a').mp h
      exact (leGlueGen_tagA_tagA_iff m' hm' (g a) (g a')).mpr (g.monotone hle)
    | inr y =>
      cases y with
      | inl b =>
        by_cases hbtop : b = ⊤
        · subst hbtop
          rw [glueTwist_inr_inl, hpsit]
          exact leGlue_tagA_tagB_topGen m' (g a)
        · have ham : a ≤ m := le_marked_of_leGlueGen_tagB m a b hbtop h
          exact ⟨Sum.inl (g a), self_mem_occsGen _ _,
                 Sum.inr (Sum.inl (ψ b)), self_mem_occsGen _ _,
                 hgm ▸ g.monotone ham⟩
      | inr c' => exact leGlueGen_tagA_tagC m' (g a) (g c')
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagB_tagAGen m b a' hm hbt hbne)
      | inr y =>
        cases y with
        | inl b' =>
          by_cases hb'top : b' = ⊤
          · subst hb'top
            rw [glueTwist_inr_inl, glueTwist_inr_inl, hpsit]
            exact leGlueGen_tagB_tagBtop m' (ψ b)
          · have hle : b ≤ b' := le_of_leGlueGen_tagB_tagB m b b' hb'top h
            exact ⟨Sum.inr (Sum.inl (ψ b)), self_mem_occsGen _ _,
                   Sum.inr (Sum.inl (ψ b')), self_mem_occsGen _ _, ψ.monotone hle⟩
        | inr c' =>
          have hmc : m ≤ c' := marked_le_of_leGlueGen_tagB_tagC m b c' h
          exact ⟨Sum.inr (Sum.inl (ψ b)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr (g c')), self_mem_occsGen _ _,
                 hgm ▸ g.monotone hmc⟩
    | inr c =>
      have hcne : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagC_tagAGen m c a' hcne)
      | inr y =>
        cases y with
        | inl b' =>
          have hb'top : b' = ⊤ := by
            by_contra hcon
            exact not_leGlue_tagC_tagBGen m c b' hcon h
          subst hb'top
          have hcm : c ≤ m := by
            obtain ⟨u, hu, v, hv, huv⟩ := h
            have hu' : u = Sum.inr (Sum.inr c) := occsGen_tagC m c u hu
            subst hu'
            rcases occsGen_tagB m (⊤ : P) v hv with hv' | ⟨_, hv'⟩
            · subst hv'; exact huv.elim
            · subst hv'; exact huv
          rw [glueTwist_inr_inl, hpsit]
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr m'), by simp [occsGen],
                 hgm ▸ g.monotone hcm⟩
        | inr c' =>
          obtain ⟨u, hu, v, hv, huv⟩ := h
          have hu' : u = Sum.inr (Sum.inr c) := occsGen_tagC m c u hu
          have hv' : v = Sum.inr (Sum.inr c') := occsGen_tagC m c' v hv
          subst hu'; subst hv'
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr (g c')), self_mem_occsGen _ _, g.monotone huv⟩

/-- **Injective when `g` and `ψ` are** — the copies do not collide, since each
lands in its own summand. -/
theorem glueTwist_injective (g ψ : P →o P') (hg : Function.Injective g)
    (hpsi : Function.Injective ψ) : Function.Injective (glueTwist g ψ) := by
  rintro (a | b | c) (a' | b' | c') h <;>
    simp only [glueTwist] at h <;>
    first
      | (injection h with h'; injection h' with h''
         first
           | exact congrArg Sum.inl (hg h'')
           | exact congrArg (Sum.inr ∘ Sum.inl) (hpsi h'')
           | exact congrArg (Sum.inr ∘ Sum.inr) (hg h''))
      | (injection h with h'; exact congrArg Sum.inl (hg h'))
      | exact absurd h (by simp)

theorem glueTwist_ne_baseMapGen (g ψ : P →o P') {b : P} (hb : ψ b ≠ g b) :
    glueTwist g ψ (Sum.inr (Sum.inl b)) ≠ baseMapGen g (Sum.inr (Sum.inl b)) := by
  intro h
  exact hb (Sum.inl.inj (Sum.inr.inj h))

/-! ## A concrete injective witness: the diamond, twisted by `Prod.swap` -/

section Diamond

/-- `Prod.swap` on the four-element diamond, as an order homomorphism.  It fixes
`⊥ = (0,0)` and `⊤ = (1,1)` and exchanges the two incomparable interior points. -/
def swapHom : (Fin 2 × Fin 2) →o (Fin 2 × Fin 2) where
  toFun := Prod.swap
  monotone' _ _ h := ⟨h.2, h.1⟩

@[simp] theorem swapHom_apply (p : Fin 2 × Fin 2) : swapHom p = Prod.swap p := rfl

theorem swapHom_injective : Function.Injective swapHom := fun _ _ h =>
  Prod.swap_injective h

theorem swapHom_top : swapHom (⊤ : Fin 2 × Fin 2) = ⊤ := by decide

theorem swapHom_ne_bot (b : Fin 2 × Fin 2) (hb : b ≠ ⊥) : swapHom b ≠ ⊥ := by
  revert hb; revert b; decide

/-- **Injectivity does not restore rigidity.**  On the diamond, with `g = id` and
`ψ = swap`, the twisted action is injective, agrees with `baseMapGen id` on
copies `A` and `C`, and differs on copy `B`. -/
theorem swapTwist_ne_baseMapGen :
    glueTwist (OrderHom.id : (Fin 2 × Fin 2) →o (Fin 2 × Fin 2)) swapHom
        (Sum.inr (Sum.inl ((0 : Fin 2), (1 : Fin 2))))
      ≠ baseMapGen (OrderHom.id : (Fin 2 × Fin 2) →o (Fin 2 × Fin 2))
        (Sum.inr (Sum.inl ((0 : Fin 2), (1 : Fin 2)))) :=
  glueTwist_ne_baseMapGen _ _ (by decide)

theorem swapTwist_injective :
    Function.Injective
      (glueTwist (OrderHom.id : (Fin 2 × Fin 2) →o (Fin 2 × Fin 2)) swapHom) :=
  glueTwist_injective _ _ (fun _ _ h => h) swapHom_injective

end Diamond

end CopyBFreedom
