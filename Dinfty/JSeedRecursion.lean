import Dinfty.AtomFactorGeneration
import Dinfty.GluingTowerLibrary

open GluingTowerLibrary

/-!
# The seed recursion, machine-checked

`AtomFactorGeneration` is the engine; this is the step it consumes.

The seed of a join-irreducible `z` is `J(↓z)` — the join-irreducibles below it.
Everything in the two-point argument rests on one computation:

> **The seed of a join-irreducible of `EndP P` is a product**: an up-set of `P`
> (dualised) times the seed of the corresponding join-irreducible of `P`.

```lean
jSeedIso (a : Pᵒᵈ) (q : J P) :
    {g : J (EndP P) // g ≤ jiOrderIso (a, q)}
      ≃o ({a' : Pᵒᵈ // a' ≤ a} × {b : J P // b ≤ q})
```

There is nothing to invent: `jiOrderIso : Pᵒᵈ × J P ≃o J (EndP P)` is already in
the library (it is what replaced the Sabidussi/Vizing axiom), an order
isomorphism restricts to principal down-sets, and a down-set in a product is the
product of the down-sets.  The recursion is those three facts composed.

## Why this is the load-bearing step

The tower's embedding is `iotaD k x = tag_A (constHom x)` and
`constHom = stepMap ⊥`, so passing one level up replaces `q` by `(⊥, q)` — the
**first coordinate is `⊥`**, and `{a' : Pᵒᵈ // a' ≤ toDual ⊥}` is all of `Pᵒᵈ`
(`downSet_toDual_bot`).  That is why the marked point's seed picks up a *full*
`(D k)ᵒᵈ` factor at every level while a competitor `stepMap p q` with `p ≠ ⊥`
picks up only `(↑p)ᵒᵈ`, which is strictly smaller.

Cardinality then forces `p = ⊥` — the step that makes the induction go — and
`AtomFactorGeneration.not_genByFactors_of_strict_upper` kills the copy-`B` and
copy-`C` competitors, whose seeds are ordinal sums rather than products.

## What is still missing

The colimit assembly: that `JBelow z` in `DInfty` is the colimit of these
level-wise seeds, and that the colimit of `Pₖᵒᵈ × (−)` is the restricted product
`AtomFactorGeneration` knows how to handle.  Until that exists,
`TwoPointFixed` stays open; see `Dinfty/SeedShape.lean`, which states it as a
hypothesis and runs the rest of the argument against it.
-/

open scoped Classical

universe u v

namespace JSeedRecursion

/-! ## Two general facts -/

/-- An order isomorphism restricts to principal down-sets. -/
def downSetIso {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
    (e : X ≃o Y) (x : X) : {u : X // u ≤ x} ≃o {v : Y // v ≤ e x} where
  toFun u := ⟨e u.1, e.monotone u.2⟩
  invFun v := ⟨e.symm v.1, by
    have h := e.symm.monotone v.2
    rwa [e.symm_apply_apply] at h⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.1)
  right_inv v := Subtype.ext (e.apply_symm_apply v.1)
  map_rel_iff' := e.map_rel_iff

/-- A principal down-set in a product is the product of the down-sets. -/
def prodDownSetIso {A : Type u} {B : Type u} [Preorder A] [Preorder B] (p : A × B) :
    {u : A × B // u ≤ p} ≃o ({a : A // a ≤ p.1} × {b : B // b ≤ p.2}) where
  toFun u := (⟨u.1.1, u.2.1⟩, ⟨u.1.2, u.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv w := rfl
  map_rel_iff' := Iff.rfl

/-- Congruence for products (`OrderIso.prodCongr` is not in this Mathlib). -/
def prodCongrIso {A A' B B' : Type u} [Preorder A] [Preorder A'] [Preorder B]
    [Preorder B'] (e : A ≃o A') (f : B ≃o B') : (A × B) ≃o (A' × B') where
  toFun p := (e p.1, f p.2)
  invFun p := (e.symm p.1, f.symm p.2)
  left_inv p := Prod.ext (e.symm_apply_apply p.1) (f.symm_apply_apply p.2)
  right_inv p := Prod.ext (e.apply_symm_apply p.1) (f.apply_symm_apply p.2)
  map_rel_iff' := by
    intro p q
    exact ⟨fun h => ⟨e.le_iff_le.mp h.1, f.le_iff_le.mp h.2⟩,
           fun h => ⟨e.monotone h.1, f.monotone h.2⟩⟩

/-! ## The recursion -/

section Seed

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
variable [UniqueAtomCoatom P]

/-- **The seed of a join-irreducible of `EndP P` is a product.**

`jiOrderIso` names the join-irreducibles of `EndP P` as pairs `(a, q)` with
`a : Pᵒᵈ` and `q` join-irreducible in `P`; restricting it to the down-set of
`(a, q)` and splitting the product gives the recursion. -/
noncomputable def jSeedIso (a : Pᵒᵈ) (q : {x : P // JoinIrred P x}) :
    {g : {f : EndP P // JoinIrred (EndP P) f} // g ≤ jiOrderIso (a, q)}
      ≃o ({a' : Pᵒᵈ // a' ≤ a} × {b : {x : P // JoinIrred P x} // b ≤ q}) :=
  (downSetIso jiOrderIso (a, q)).symm.trans (prodDownSetIso ((a, q) : Pᵒᵈ × _))

/-- **At the marked point the first factor is everything.**  The tower embeds by
`constHom = stepMap ⊥`, i.e. by `a = toDual ⊥`, and then the up-set factor is all
of `Pᵒᵈ` — which is why the marked point's seed gains a full `(D k)ᵒᵈ` at every
level. -/
def downSet_toDual_bot : {a' : Pᵒᵈ // a' ≤ OrderDual.toDual (⊥ : P)} ≃o Pᵒᵈ where
  toFun a := a.1
  invFun a := ⟨a, by
    show (⊥ : P) ≤ OrderDual.ofDual a
    exact bot_le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The marked-point instance of the recursion: the seed of `constHom q` is
`Pᵒᵈ` times the seed of `q`. -/
noncomputable def jSeedIso_bot (q : {x : P // JoinIrred P x}) :
    {g : {f : EndP P // JoinIrred (EndP P) f} //
        g ≤ jiOrderIso (OrderDual.toDual (⊥ : P), q)}
      ≃o (Pᵒᵈ × {b : {x : P // JoinIrred P x} // b ≤ q}) :=
  (jSeedIso (OrderDual.toDual (⊥ : P)) q).trans
    (prodCongrIso downSet_toDual_bot (OrderIso.refl _))

/-- **A competitor's first factor is strictly smaller.**  If `p ≠ ⊥` then the
up-set factor of `stepMap p q`'s seed omits `⊥`, so it cannot be all of `Pᵒᵈ`
— this is the cardinality step that forces `p = ⊥` in the induction. -/
theorem downSet_ne_univ_of_ne_bot {p : P} (hp : p ≠ ⊥) :
    ¬ ∀ a' : Pᵒᵈ, a' ≤ OrderDual.toDual p := by
  intro h
  have h1 : p ≤ (⊥ : P) := h (OrderDual.toDual (⊥ : P))
  exact hp (le_bot_iff.mp h1)

end Seed

end JSeedRecursion
