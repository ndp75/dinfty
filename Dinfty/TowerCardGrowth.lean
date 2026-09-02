import Dinfty.WeakProdFactorization
import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

-- [D-1865] §The-three-cardinality-facts-the-copy-A-step
open scoped Classical

universe u

namespace TowerCardGrowth

-- [D-1866] §The-tower-grows
-- [D-1867] card_D_lt_succ
theorem card_D_lt_succ (k : ℕ) : Fintype.card (D k) < Fintype.card (D (k + 1)) := by
  refine Fintype.card_lt_of_injective_of_notMem (iotaD k) (iotaD_injective k)
    (b := (⊤ : D (k + 1))) ?_
  rintro ⟨x, hx⟩
  exact iotaD_ne_top k x hx

-- [D-1868] card_D_strictMono
theorem card_D_strictMono : StrictMono (fun k => Fintype.card (D k)) :=
  strictMono_nat_of_lt_succ card_D_lt_succ

-- [D-1869] card_D_lt_of_lt
theorem card_D_lt_of_lt {i j : ℕ} (h : i < j) :
    Fintype.card (D i) < Fintype.card (D j) := card_D_strictMono h

-- [D-1870] §Join-irreducibles-are-a-proper-subtype
-- [D-1871] card_joinIrred_lt
theorem card_joinIrred_lt {P : Type u} [Fintype P] [Lattice P] [OrderBot P]
    [Nontrivial P] :
    Fintype.card {x : P // JoinIrred P x} < Fintype.card P := by
  refine Fintype.card_lt_of_injective_of_notMem (fun x => x.1)
    (fun _ _ h => Subtype.ext h) (b := (⊥ : P)) ?_
  rintro ⟨⟨x, hx⟩, hxv⟩
  exact hx.1 hxv

-- [D-1872] §A-proper-up-set-is-smaller
-- [D-1873] card_upSet_lt
theorem card_upSet_lt {P : Type u} [Fintype P] [PartialOrder P] [OrderBot P]
    {p : P} (hp : p ≠ ⊥) :
    Fintype.card {a : P // p ≤ a} < Fintype.card P := by
  refine Fintype.card_lt_of_injective_of_notMem (fun a => a.1)
    (fun _ _ h => Subtype.ext h) (b := (⊥ : P)) ?_
  rintro ⟨⟨a, ha⟩, hav⟩
  exact hp (le_bot_iff.mp (hav ▸ ha))

-- [D-1874] card_upSet_eq_of_bot
theorem card_upSet_eq_of_bot {P : Type u} [Fintype P] [PartialOrder P] [OrderBot P] :
    Fintype.card {a : P // (⊥ : P) ≤ a} = Fintype.card P :=
  Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => bot_le))

end TowerCardGrowth
