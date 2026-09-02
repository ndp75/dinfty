import Dinfty.EndLocalContinuity

open GluingTowerLibrary SierpinskiApplication

/-!
# How rigid is the `Gen`-layer morphism action?

The load-bearing open step in the ingredient-3 chain is an *identification*:
that the `Gen`-layer action `baseMapGen` and `Φ_tri_v2`'s morphism action are
the same map.  Identifications are closed by rigidity — if a characterization
admits only one map and both satisfy it, they are equal — so the question worth
settling is exactly which data pins `baseMapGen`.

**Answer: the three copies, separately.  Copy `A` alone is not enough, and the
gap is not a technicality.**

* `baseMapGen_unique` — the positive half, and it is deliberately unglamorous:
  agreeing with `g` on each of the three copies characterizes `baseMapGen g`.
  This is what an identification with `Φ_tri_v2` has to supply.
* `collapseB` — the negative half.  A map that agrees with `baseMapGen g` on
  copy `A` **and** on copy `C`, is monotone for the glued order, and is
  well-defined on the canon-fixed region, but differs from it on copy `B`: it
  sends every copy-`B` point to the seam `tag_B ⊤`.

So an identification cannot be obtained as a copy-`A` corollary, and not from
copies `A` and `C` together either, however much naturality is available there.
The `Gen`-layer action is genuinely not unique at these hypotheses — with the
caveat below on what that leaves open.

## Why `collapseB` is monotone

Because the glued order gives copy `B` very little room above copy `A` and very
little room below copy `C`, and the seam `tag_B ⊤` sits exactly at the top of
that room.  The nine tag-pairs:

* copy `A` → copy `A`, and copy `C` → copy `C`: `g` monotone;
* copy `A` → copy `B`: free — everything in copy `A` is below `tag_B ⊤`, via
  that point's copy-`C` occurrence `tag_C m'`;
* copy `A` → copy `C`: free (`rawRuleGen` is `True` there);
* copy `B` → copy `B`: both sides land on `tag_B ⊤`, so reflexivity;
* copy `B` → copy `C`: the hypothesis gives `m ≤ c'`, and `g m = m'` carries it;
* copy `C` → copy `B`: only reachable at `b' = ⊤`, and then the hypothesis
  gives `c ≤ m`, which `g m = m'` again carries;
* copy `B` → copy `A` and copy `C` → copy `A`: impossible on canon-fixed points.

Note where the tripointedness hypotheses are spent: **only `g m = m'`**, twice.
`g ⊥ = ⊥` and injectivity are used for well-definedness on the canon-fixed
region, not for monotonicity.

## The caveat, and the sharper question this leaves

`collapseB` is not injective, and `baseMapGen g` is (for injective `g`), so one
might hope **injectivity** restores rigidity — that being the form
`NormalizedGlueMap`'s `glueMap` assumes.  **It does not.**
`Dinfty/CopyBFreedom.lean` generalises `collapseB` to `glueTwist g ψ` for an
arbitrary monotone `ψ`, shows it is injective whenever `g` and `ψ` are, and
exhibits an injective witness on the four-element diamond with `ψ = Prod.swap`.
The copy-`B` component is simply free; see that module for why the glued order
does not couple it to the other two copies.
-/

open scoped Classical

universe u v

namespace BaseMapGenRigidity

open GenContinuity EndLocalContinuity

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

/-! ## The positive half: copy-wise agreement characterises the action -/

/-- **What an identification must supply.**  Agreement with `g` on each of the
three copies pins `baseMapGen g` completely.  Unglamorous by design: the content
is that all three are needed, which is the negative half below. -/
theorem baseMapGen_unique (g : P →o P') (H : GlueBaseGen P → GlueBaseGen P')
    (hA : ∀ x, H (Sum.inl x) = Sum.inl (g x))
    (hB : ∀ x, H (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl (g x)))
    (hC : ∀ x, H (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr (g x))) :
    H = baseMapGen g := by
  funext x
  cases x with
  | inl a => exact hA a
  | inr x =>
    cases x with
    | inl b => exact hB b
    | inr c => exact hC c

/-! ## The negative half: copy `A` (and even copy `C`) is not enough -/

/-- The copy-`B`-collapsing map: `baseMapGen g` on copies `A` and `C`, and
constantly the seam `tag_B ⊤` on copy `B`. -/
def collapseB (g : P →o P') : GlueBaseGen P → GlueBaseGen P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl (⊤ : P'))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

@[simp] theorem collapseB_inl (g : P →o P') (a : P) :
    collapseB g (Sum.inl a) = Sum.inl (g a) := rfl

@[simp] theorem collapseB_inr_inr (g : P →o P') (c : P) :
    collapseB g (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr (g c)) := rfl

/-- It agrees with the real action on copy `A` … -/
theorem collapseB_eq_on_tagA (g : P →o P') (a : P) :
    collapseB g (Sum.inl a) = baseMapGen g (Sum.inl a) := rfl

/-- … and on copy `C` as well. -/
theorem collapseB_eq_on_tagC (g : P →o P') (c : P) :
    collapseB g (Sum.inr (Sum.inr c)) = baseMapGen g (Sum.inr (Sum.inr c)) := rfl

/-- **Well-defined on the canon-fixed region**, given the same hypotheses
`NormalizedGlueMap` asks of a morphism: `⊥`-preservation, `m ↦ m'`, and
injectivity. -/
theorem collapseB_canonGen_fixed (m : P) (m' : P') (g : P →o P')
    (hgb : g ⊥ = ⊥) (hgm : g m = m') (hginj : Function.Injective g)
    (hbt' : (⊥ : P') ≠ ⊤) {x : GlueBaseGen P} (hx : canonGen m x = x) :
    canonGen m' (collapseB g x) = collapseB g x := by
  cases x with
  | inl a => rfl
  | inr x =>
    cases x with
    | inl b =>
      show canonGen m' (Sum.inr (Sum.inl (⊤ : P'))) = Sum.inr (Sum.inl (⊤ : P'))
      simp only [canonGen]; rw [if_neg (Ne.symm hbt')]
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

/-- **Monotone for the glued order**, on canon-fixed points.  The only
tripointedness input is `g m = m'`, used in the two cross-copy cases. -/
theorem collapseB_monotone (m : P) (m' : P') (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt : (⊥ : P) ≠ ⊤) (g : P →o P')
    (hgm : g m = m') {x y : GlueBaseGen P}
    (hx : canonGen m x = x) (hy : canonGen m y = y)
    (h : leGlueGen m x y) :
    leGlueGen m' (collapseB g x) (collapseB g y) := by
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      have : a ≤ a' := (leGlueGen_tagA_tagA_iff m hm a a').mp h
      exact (leGlueGen_tagA_tagA_iff m' hm' (g a) (g a')).mpr (g.monotone this)
    | inr y =>
      cases y with
      | inl _ => exact leGlue_tagA_tagB_topGen m' (g a)
      | inr c' => exact leGlueGen_tagA_tagC m' (g a) (g c')
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      cases y with
      | inl a' =>
        exact absurd h (not_leGlue_tagB_tagAGen m b a' hm hbt hbne)
      | inr y =>
        cases y with
        | inl _ => exact leGlueGen_refl m' _
        | inr c' =>
          have hmc : m ≤ c' := marked_le_of_leGlueGen_tagB_tagC m b c' h
          exact ⟨Sum.inr (Sum.inl (⊤ : P')), self_mem_occsGen _ _,
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
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr m'), by simp [collapseB, occsGen],
                 hgm ▸ g.monotone hcm⟩
        | inr c' =>
          obtain ⟨u, hu, v, hv, huv⟩ := h
          have hu' : u = Sum.inr (Sum.inr c) := occsGen_tagC m c u hu
          have hv' : v = Sum.inr (Sum.inr c') := occsGen_tagC m c' v hv
          subst hu'; subst hv'
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr (g c')), self_mem_occsGen _ _, g.monotone huv⟩

/-- **And it differs from the real action**, as soon as some copy-`B` point is
not already at the seam. -/
theorem collapseB_ne_baseMapGen (g : P →o P') {b : P} (hb : g b ≠ ⊤) :
    collapseB g (Sum.inr (Sum.inl b)) ≠ baseMapGen g (Sum.inr (Sum.inl b)) := by
  intro h
  exact hb (Sum.inl.inj (Sum.inr.inj h)).symm

end BaseMapGenRigidity
