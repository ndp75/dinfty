import Dinfty.WeakProdFactorization
import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

/-!
# The three cardinality facts the copy-`A` step needs

`WeakProdFactorization.factor_of_prod` says every atom-factor of a competitor's
finite seed is isomorphic to *some* `D j`.  Turning that into "some `D j` with
`j < N`" needs the tower to grow, and pinning `p = ⊥` needs a proper up-set to
be strictly smaller.  All three are one-liners once the right existing lemma is
named.

* `card_D_lt_succ` — `iotaD k` is an injection `D k → D (k+1)` that **misses the
  top** (`iotaD_ne_top`), so the levels grow strictly.  No counting formula for
  `GlueCar` is needed.
* `card_joinIrred_lt` — `⊥` is never join-irreducible, so `J P` is a proper
  subtype of `P`.
* `card_upSet_lt` — a proper up-set misses `⊥`.

Together with `WeakProdFactorization.factor_index_lt` these are exactly the
inputs listed in `Dinfty/SeedShape.lean`'s docstring as "two `Fintype.card`
inequalities about the tower, stated but not proved".  They are proved now.

**This still does not close `TwoPointFixed`** — the colimit shape (input 1) is
untouched, and the copy-`A` induction has to be assembled against it.  What is
gone is the excuse that the cardinality side was unexamined.
-/

open scoped Classical

universe u

namespace TowerCardGrowth

/-! ## The tower grows -/

/-- **Each level is strictly bigger than the last.**  `iotaD k` embeds `D k`
into `D (k+1)` and misses `⊤`. -/
theorem card_D_lt_succ (k : ℕ) : Fintype.card (D k) < Fintype.card (D (k + 1)) := by
  refine Fintype.card_lt_of_injective_of_notMem (iotaD k) (iotaD_injective k)
    (b := (⊤ : D (k + 1))) ?_
  rintro ⟨x, hx⟩
  exact iotaD_ne_top k x hx

theorem card_D_strictMono : StrictMono (fun k => Fintype.card (D k)) :=
  strictMono_nat_of_lt_succ card_D_lt_succ

theorem card_D_lt_of_lt {i j : ℕ} (h : i < j) :
    Fintype.card (D i) < Fintype.card (D j) := card_D_strictMono h

/-! ## Join-irreducibles are a proper subtype -/

/-- `⊥` is never join-irreducible, so there are strictly fewer join-irreducibles
than elements. -/
theorem card_joinIrred_lt {P : Type u} [Fintype P] [Lattice P] [OrderBot P]
    [Nontrivial P] :
    Fintype.card {x : P // JoinIrred P x} < Fintype.card P := by
  refine Fintype.card_lt_of_injective_of_notMem (fun x => x.1)
    (fun _ _ h => Subtype.ext h) (b := (⊥ : P)) ?_
  rintro ⟨⟨x, hx⟩, hxv⟩
  exact hx.1 hxv

/-! ## A proper up-set is smaller -/

/-- A proper up-set misses `⊥`. -/
theorem card_upSet_lt {P : Type u} [Fintype P] [PartialOrder P] [OrderBot P]
    {p : P} (hp : p ≠ ⊥) :
    Fintype.card {a : P // p ≤ a} < Fintype.card P := by
  refine Fintype.card_lt_of_injective_of_notMem (fun a => a.1)
    (fun _ _ h => Subtype.ext h) (b := (⊥ : P)) ?_
  rintro ⟨⟨a, ha⟩, hav⟩
  exact hp (le_bot_iff.mp (hav ▸ ha))

/-- …and the whole up-set is recovered exactly at `⊥`. -/
theorem card_upSet_eq_of_bot {P : Type u} [Fintype P] [PartialOrder P] [OrderBot P] :
    Fintype.card {a : P // (⊥ : P) ≤ a} = Fintype.card P :=
  Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => bot_le))

end TowerCardGrowth
