import Dinfty.WeakProductAbsorption
import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

/-!
# The tower's own family satisfies both hypotheses

`WeakProductAbsorption.weakProd_no_absorb_two` is abstract: a restricted product
absorbs no two-element factor as soon as every factor has a least non-`⊥`
element and a third element.  The tower supplies both, at every level, and this
module says so.

* **Least non-`⊥` element** — `realUniqueAtomCoatom k`, i.e.
  `UniqueAtomCoatom.unique_atom`, which is exactly the property
  `Indecomposable` isolated as the fixed-point obstruction.  `atomOf (D k)` is
  the element and `atomOf_le` is the property.
* **A third element** — `⊤ : D k`, which is neither `⊥` (nontriviality) nor the
  atom (`atomOf_ne_top`, proved here from `dMid k ≠ ⊤`).

So

```lean
tower_no_absorb_two : IsEmpty (WeakProd D ≃o (WeakProd D × Fin 2))
```

## Reading it against `§17`

`§17`'s objects are `colim S_k` with `S_{k+1} = S_k × (D k)ᵒᵖ`, unfolded by
`Indecomposable` to `⨁_j (D j)ᵒᵖ` and `C₂ × ⨁_j (D j)ᵒᵖ`.  The basepoint of the
colimit is `⊤` in each `(D j)ᵒᵖ` — the dual of `⊥` in `D j` — so the object is
the **order dual** of `WeakProd D`, and `C₂` is self-dual.  Since `A ≃o B` iff
`Aᵒᵈ ≃o Bᵒᵈ`, the statement above is the statement about `§17`'s objects.

**The two seeds do not collide.**  That was the last route by which `↓midInf`
and `↓(toD 0 ⊤)` could have been identified, and it is closed.

## What is still missing for `TwoPointFixed`

Exactly what `WeakProductAbsorption`'s docstring lists, and it is worth
repeating because the gap is easy to lose:

1. the identification of `JBelow midInf` and `JBelow (toD 0 ⊤)` with these two
   restricted products is **not formalised** — it is the down-set /
   join-irreducible recursion carried to the colimit;
2. and seed separation asks that **no element of any stage** shares `midInf`'s
   seed, not merely that `toD 0 ⊤` does not.

This module closes a named sub-question.  It does not close pillar B's base
case, and should not be cited as doing so.
-/

open scoped Classical

namespace TowerNoAbsorption

open WeakProductAbsorption

/-- The tower's least non-`⊥` element at level `k`. -/
noncomputable def lamD (k : ℕ) : D k :=
  letI := realUniqueAtomCoatom k
  atomOf (D k)

theorem lamD_ne_bot (k : ℕ) : lamD k ≠ (⊥ : D k) := by
  letI := realUniqueAtomCoatom k
  exact atomOf_ne_bot (D k)

theorem lamD_le (k : ℕ) (z : D k) (hz : z ≠ ⊥) : lamD k ≤ z := by
  letI := realUniqueAtomCoatom k
  exact atomOf_le hz

/-- `⊤` is a third element: the least non-`⊥` element is not the top, because it
sits below the marked point and the marked point is not the top. -/
theorem lamD_ne_top (k : ℕ) : (⊤ : D k) ≠ lamD k := by
  intro hcon
  refine dMid_ne_top k ?_
  have h1 : lamD k ≤ dMid k := lamD_le k (dMid k) (dMid_ne_bot k)
  rw [← hcon] at h1
  exact le_antisymm le_top h1

theorem top_ne_bot_D (k : ℕ) : (⊤ : D k) ≠ (⊥ : D k) := by
  letI := (towerLevel k).nontriv
  exact fun h => (bot_ne_top_of_nontrivial (P := D k)) h.symm

/-- **The tower's restricted product absorbs no two-element factor.**

Both hypotheses come from the tower itself: `realUniqueAtomCoatom` for the least
non-`⊥` element, and `⊤` for the third element. -/
theorem tower_no_absorb_two :
    IsEmpty (WeakProd (fun k => D k) ≃o (WeakProd (fun k => D k) × Fin 2)) :=
  weakProd_no_absorb_two lamD lamD_ne_bot lamD_le (fun k => (⊤ : D k))
    top_ne_bot_D lamD_ne_top

end TowerNoAbsorption
