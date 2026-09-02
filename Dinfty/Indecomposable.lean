import Dinfty.SeedContrast

open GluingTowerLibrary SierpinskiApplication

-- [D-1717] §Stop-iterating-solve-the-recursion-at-the-level
open scoped Classical

namespace Indecomposable

-- [D-1718] §The-fixed-point-obstruction
-- [D-1719] not_iso_prod_of_least_nonbot
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

-- [D-1720] DirectlyIndecomposable
def DirectlyIndecomposable (P : Type*) [Lattice P] [OrderBot P] : Prop :=
  ∀ (A B : Type) (_ : Lattice A) (_ : OrderBot A) (_ : Lattice B) (_ : OrderBot B)
    (_ : P ≃o A × B) (a : A) (_ : a ≠ ⊥) (b : B) (_ : b ≠ ⊥), False

-- [D-1721] directlyIndecomposable_of_least_nonbot
theorem directlyIndecomposable_of_least_nonbot {P : Type} [Lattice P] [OrderBot P]
    (lam : P) (hlam : lam ≠ ⊥) (hle : ∀ z : P, z ≠ ⊥ → lam ≤ z) :
    DirectlyIndecomposable P :=
  fun _A _B _ _ _ _ e a ha b hb => not_iso_prod_of_least_nonbot lam hlam hle e ha hb

-- [D-1722] §Every-level-of-the-tower
-- [D-1723] D_directlyIndecomposable
theorem D_directlyIndecomposable (k : ℕ) : DirectlyIndecomposable (D k) := by
  letI := realUniqueAtomCoatom k
  obtain ⟨lam, ⟨hlam, hle⟩, -⟩ := (UniqueAtomCoatom.unique_atom (P := D k))
  exact directlyIndecomposable_of_least_nonbot lam hlam hle

-- [D-1724] D_card_ne_two
theorem D_card_ne_two (k : ℕ) : Fintype.card (D k) ≠ 2 := by
  have h := D_card_ge_three k
  omega

end Indecomposable
