import Dinfty.Height
import Dinfty.Truncation

-- [D-3050] §The-seed-comparison-replumbed
open scoped Classical

universe u

namespace SeedComparison

open WeakProductAbsorption AtomFactorGeneration Height Truncation

-- [D-3051] §Atoms-of-a-product
section Atoms

variable {A : Type u} {B : Type u}
variable [PartialOrder A] [OrderBot A] [PartialOrder B] [OrderBot B]

-- [D-3052] atomsProdEquiv
noncomputable def atomsProdEquiv :
    {p : A × B // IsAtom p} ≃ ({a : A // IsAtom a} ⊕ {b : B // IsAtom b}) where
  toFun p :=
    if h : p.1.2 = ⊥ then
      Sum.inl ⟨p.1.1, by
        rcases prodIsAtom_iff.mp p.2 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact h1
        · exact absurd rfl (h ▸ h2).1⟩
    else
      Sum.inr ⟨p.1.2, by
        rcases prodIsAtom_iff.mp p.2 with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd h2 h
        · exact h2⟩
  invFun s :=
    s.elim (fun a => ⟨(a.1, ⊥), prodIsAtom_iff.mpr (Or.inl ⟨a.2, rfl⟩)⟩)
           (fun b => ⟨(⊥, b.1), prodIsAtom_iff.mpr (Or.inr ⟨rfl, b.2⟩)⟩)
  left_inv p := by
    by_cases h : p.1.2 = ⊥
    · simp only [dif_pos h, Sum.elim_inl]
      exact Subtype.ext (Prod.ext rfl h.symm)
    · simp only [dif_neg h, Sum.elim_inr]
      refine Subtype.ext (Prod.ext ?_ rfl)
      rcases prodIsAtom_iff.mp p.2 with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 h
      · exact h1.symm
  right_inv s := by
    rcases s with ⟨a, ha⟩ | ⟨b, hb⟩
    · simp
    · have hb' : ¬ ((⊥ : A), b).2 = ⊥ := hb.1
      simp only [Sum.elim_inr, dif_neg hb']

-- [D-3053] card_atoms_prod
theorem card_atoms_prod [Finite A] [Finite B] :
    Nat.card {p : A × B // IsAtom p}
      = Nat.card {a : A // IsAtom a} + Nat.card {b : B // IsAtom b} := by
  rw [Nat.card_congr atomsProdEquiv, Nat.card_sum]

end Atoms

-- [D-3054] §Transporting-atoms
section AtomsIso

variable {L : Type u} {L' : Type u} [PartialOrder L] [OrderBot L]
variable [PartialOrder L'] [OrderBot L']

-- [D-3055] atomsIso
def atomsIso (f : L ≃o L') : {a : L // IsAtom a} ≃ {b : L' // IsAtom b} where
  toFun a := ⟨f a.1, orderIso_isAtom f a.2⟩
  invFun b := ⟨f.symm b.1, orderIso_isAtom f.symm b.2⟩
  left_inv a := by simp
  right_inv b := by simp

end AtomsIso

-- [D-3056] §The-three-necessary-equations
section Package

variable {D : ℕ → Type u} {E : ℕ → Type u} {T : Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ i, PartialOrder (E i)] [∀ i, OrderBot (E i)]
variable [PartialOrder T] [OrderBot T] [IsAtomic T]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamD : ∀ j, D j) (lamE : ∀ i, E i)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ i, lamE i ≠ ⊥) (hE_le : ∀ i (z : E i), z ≠ ⊥ → lamE i ≤ z)

-- [D-3057] card_atoms_eq
include hD_ne hD_le hE_ne hE_le in
theorem card_atoms_eq [Finite T] [Finite S] (N : ℕ)
    [Finite ↥(weakBelow D N)]
    (e : (WeakProd D × T) ≃o (WeakProd E × S))
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N) :
    Nat.card {β : S // IsAtom β}
      = Nat.card {w : ↥(weakBelow D N) // IsAtom w} + Nat.card {τ : T // IsAtom τ} := by
  have f := (seed_iso_prod lamD lamE hD_ne hD_le hE_ne hE_le e N hbig hS hT).some
  rw [← Nat.card_congr (atomsIso f), card_atoms_prod]

-- [D-3058] htP_eq
include hD_ne hD_le hE_ne hE_le in
theorem htP_eq [Fintype T] [Fintype S] [Nonempty T] (N : ℕ)
    [Fintype ↥(weakBelow D N)] [Nonempty ↥(weakBelow D N)]
    (e : (WeakProd D × T) ≃o (WeakProd E × S))
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N) :
    htP S = htP ↥(weakBelow D N) + htP T := by
  have f := (seed_iso_prod lamD lamE hD_ne hD_le hE_ne hE_le e N hbig hS hT).some
  rw [← htP_orderIso f, htP_prod]

-- [D-3059] §The-refutations
-- [D-3060] no_iso_of_card_ne
include hD_ne hD_le hE_ne hE_le in
theorem no_iso_of_card_ne [Finite T] [Finite S] (N : ℕ) (I : Finset ℕ)
    (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I)
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N)
    (hne : Nat.card S ≠ (∏ j ∈ I, Nat.card (D j)) * Nat.card T) :
    IsEmpty ((WeakProd D × T) ≃o (WeakProd E × S)) :=
  ⟨fun e => hne (card_eq_prod lamD lamE hD_ne hD_le hE_ne hE_le e N hbig hS hT I hI)⟩

-- [D-3061] no_iso_of_atoms_ne
include hD_ne hD_le hE_ne hE_le in
theorem no_iso_of_atoms_ne [Finite T] [Finite S] (N : ℕ)
    [Finite ↥(weakBelow D N)]
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N)
    (hne : Nat.card {β : S // IsAtom β}
      ≠ Nat.card {w : ↥(weakBelow D N) // IsAtom w} + Nat.card {τ : T // IsAtom τ}) :
    IsEmpty ((WeakProd D × T) ≃o (WeakProd E × S)) :=
  ⟨fun e => hne (card_atoms_eq lamD lamE hD_ne hD_le hE_ne hE_le N e hbig hS hT)⟩

-- [D-3062] no_iso_of_htP_ne
include hD_ne hD_le hE_ne hE_le in
theorem no_iso_of_htP_ne [Fintype T] [Fintype S] [Nonempty T] (N : ℕ)
    [Fintype ↥(weakBelow D N)] [Nonempty ↥(weakBelow D N)]
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N)
    (hne : htP S ≠ htP ↥(weakBelow D N) + htP T) :
    IsEmpty ((WeakProd D × T) ≃o (WeakProd E × S)) :=
  ⟨fun e => hne (htP_eq lamD lamE hD_ne hD_le hE_ne hE_le N e hbig hS hT)⟩

end Package

end SeedComparison
