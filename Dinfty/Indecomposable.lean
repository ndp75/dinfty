import Dinfty.SeedContrast

open GluingTowerLibrary SierpinskiApplication

/-!
# Stop iterating: solve the recursion at the level of its factors

Every reduction in this thread has landed on the same shape:

```
T_{k+1} = T_k × (D k)ᵒᵖ
```

— §7's join-irreducible family, §7s's `J(P) × Pᵒᵖ`, `card_joinIrred_D_succ`, the
`D_2` sweep, and now §17's two seeds.  That is not a run of coincidences.
`iotaD k` is `glueA (markedPt k) ∘ constHom`, and `constHom x = stepMap x ⊥`; so
passing one level up adjoins **exactly one** free threshold coordinate ranging
over `D k`, contravariantly.  *Any* down-set-shaped invariant therefore picks up
one `(D k)ᵒᵖ` factor per level, forever.  Re-deriving it in a new direction
produces the same wall in new coordinates, which is what has happened each time.

So the move is not another reduction.  It is to say something about the
**factors**, uniformly in `k` — a statement at the fixed point of the recursion
rather than at any stage of it.  That is what this module does.

## The fixed-point statement

`§17` left: are `colim S_k` and `colim (2 × S_k)` isomorphic, where
`S_{k+1} = S_k × (D k)ᵒᵖ`?  Unfolded, the objects are restricted products
`⨁_j (D j)ᵒᵖ` and `C₂ × ⨁_j (D j)ᵒᵖ`.  An isomorphism would have to *absorb* a
two-element factor.  The obstruction is a property of the factors:

```lean
not_iso_prod_of_least_nonbot :
  P has a least non-⊥ element  →  P ≇ A × B  for nontrivial A, B
```

**and every `D k` has one** — that is exactly `UniqueAtomCoatom.unique_atom`,
which the tower carries at every level (`realUniqueAtomCoatom`).  Hence
`D_directly_indecomposable`: no level of the tower is a nontrivial direct
product, uniformly in `k`, by an argument with no induction and no finiteness in
it.

The proof is three lines and worth stating: if `λ` is least among non-`⊥`
elements and `P ≃o A × B` with both factors nontrivial, then `(a, ⊥)` and
`(⊥, b)` are both non-`⊥`, so `λ` is below both, so `λ ≤ (a,⊥) ⊓ (⊥,b) = ⊥`.

## What it settles, and what it does not

**Settles:** no `D k` contributes a `C₂` factor, and none can be split to make
room for one.  So `C₂ × X ≅ X` cannot happen by any *finite* rearrangement of
the factors — the two down-sets of §17 are not going to be identified by
regrouping.  Any isomorphism must be a genuinely infinite phenomenon, of the
`A^ℕ ≅ A × A^ℕ` kind, which needs repetition among the factors.

**Does not settle:** whether such an infinite absorption exists here.  The
factors `(D j)ᵒᵖ` are pairwise non-isomorphic (their cardinalities differ), so
the usual shift trick has nothing to shift; but "no shift" is not a proof, and
unique factorization can fail for infinite products.  That is the remaining
question, and it is now about a product of pairwise-distinct indecomposables —
a question in poset algebra, not about `DInfty`.
-/

open scoped Classical

namespace Indecomposable

/-! ## The fixed-point obstruction -/

/-- **A lattice with a least non-`⊥` element is directly indecomposable.**

No finiteness, no induction, no atoms — just the meet.  If `λ` is below every
non-`⊥` element and `P ≃o A × B` with `a ≠ ⊥` in `A` and `b ≠ ⊥` in `B`, then
`λ` sits below both `(a, ⊥)` and `(⊥, b)`, hence below their meet `⊥`. -/
theorem not_iso_prod_of_least_nonbot {P A B : Type*}
    [Lattice P] [OrderBot P] [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    (lam : P) (hlam : lam ≠ ⊥) (hle : ∀ z : P, z ≠ ⊥ → lam ≤ z)
    (e : P ≃o A × B) {a : A} (ha : a ≠ ⊥) {b : B} (hb : b ≠ ⊥) : False := by
  set p : P := e.symm (a, ⊥) with hp
  set q : P := e.symm (⊥, b) with hq
  have hpne : p ≠ ⊥ := by
    intro h
    apply ha
    have h1 : e p = e (⊥ : P) := congrArg e h
    rw [hp, e.apply_symm_apply, e.map_bot] at h1
    exact congrArg Prod.fst h1
  have hqne : q ≠ ⊥ := by
    intro h
    apply hb
    have h1 : e q = e (⊥ : P) := congrArg e h
    rw [hq, e.apply_symm_apply, e.map_bot] at h1
    exact congrArg Prod.snd h1
  have hmeet : p ⊓ q = (⊥ : P) := by
    apply e.injective
    have h1 : e (p ⊓ q) = ((a, (⊥ : B)) ⊓ ((⊥ : A), b) : A × B) := by
      rw [e.map_inf, hp, hq, e.apply_symm_apply, e.apply_symm_apply]
    rw [h1, e.map_bot]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · show a ⊓ (⊥ : A) = (⊥ : A)
      exact inf_bot_eq a
    · show (⊥ : B) ⊓ b = (⊥ : B)
      exact bot_inf_eq b
  exact hlam (le_bot_iff.mp (hmeet ▸ le_inf (hle p hpne) (hle q hqne)))

/-- Packaged: having a least non-`⊥` element rules out every nontrivial
splitting at once. -/
def DirectlyIndecomposable (P : Type*) [Lattice P] [OrderBot P] : Prop :=
  ∀ (A B : Type) (_ : Lattice A) (_ : OrderBot A) (_ : Lattice B) (_ : OrderBot B)
    (_ : P ≃o A × B) (a : A) (_ : a ≠ ⊥) (b : B) (_ : b ≠ ⊥), False

theorem directlyIndecomposable_of_least_nonbot {P : Type} [Lattice P] [OrderBot P]
    (lam : P) (hlam : lam ≠ ⊥) (hle : ∀ z : P, z ≠ ⊥ → lam ≤ z) :
    DirectlyIndecomposable P :=
  fun _A _B _ _ _ _ e a ha b hb => not_iso_prod_of_least_nonbot lam hlam hle e ha hb

/-! ## Every level of the tower -/

/-- **No level of the tower is a nontrivial direct product.**  Uniform in `k`,
from `UniqueAtomCoatom.unique_atom` — which the tower has at every level — with
no induction over `k` anywhere. -/
theorem D_directlyIndecomposable (k : ℕ) : DirectlyIndecomposable (D k) := by
  letI := realUniqueAtomCoatom k
  obtain ⟨lam, ⟨hlam, hle⟩, -⟩ := (UniqueAtomCoatom.unique_atom (P := D k))
  exact directlyIndecomposable_of_least_nonbot lam hlam hle

/-- And no level is a two-element chain either — `|D k| ≥ 3` — so the factors of
the restricted product are indecomposable **and** none of them is the `C₂` that
would have to be absorbed. -/
theorem D_card_ne_two (k : ℕ) : Fintype.card (D k) ≠ 2 := by
  have h := D_card_ge_three k
  omega

end Indecomposable
