import Mathlib.Order.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

-- [D-1431] §An-order-reflecting-join-preserving-map-has
open scoped Classical

namespace EpFromJoin

variable {α β : Type*} [Lattice α] [OrderBot α] [Fintype α] [Lattice β] [OrderBot β]

section

variable (l : α → β) (hbot : l ⊥ = ⊥) (hsup : ∀ a b, l (a ⊔ b) = l a ⊔ l b)

-- [D-1432] monotone_of_sup
include hsup in
theorem monotone_of_sup : Monotone l := by
  intro a b hab
  have h : l b = l a ⊔ l b := by rw [← hsup a b, sup_eq_right.mpr hab]
  exact h ▸ le_sup_left

-- [D-1433] map_finset_sup
include hbot hsup in
theorem map_finset_sup (s : Finset α) : l (s.sup id) = s.sup l := by
  induction s using Finset.induction_on with
  | empty => simpa using hbot
  | @insert a s _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, hsup, ih]
      rfl

-- [D-1434] upper
noncomputable def upper (y : β) : α := (Finset.univ.filter (fun x => l x ≤ y)).sup id

-- [D-1435] map_upper_le
include hbot hsup in
theorem map_upper_le (y : β) : l (upper l y) ≤ y := by
  rw [upper, map_finset_sup l hbot hsup]
  refine Finset.sup_le (fun x hx => ?_)
  exact (Finset.mem_filter.mp hx).2

-- [D-1436] le_upper
theorem le_upper (x : α) (y : β) (h : l x ≤ y) : x ≤ upper l y :=
  Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)

-- [D-1437] galoisConnection
include hbot hsup in
theorem galoisConnection : GaloisConnection l (upper l) := by
  intro x y
  constructor
  · exact le_upper l x y
  · intro h
    exact le_trans (monotone_of_sup l hsup h) (map_upper_le l hbot hsup y)

-- [D-1438] upper_monotone
include hbot hsup in
theorem upper_monotone : Monotone (upper l) := by
  intro y y' hyy'
  exact (galoisConnection l hbot hsup).monotone_u hyy'

-- [D-1439] upper_map
include hsup in
theorem upper_map (hrefl : ∀ a b : α, l a ≤ l b → a ≤ b) (x : α) : upper l (l x) = x := by
  refine le_antisymm ?_ (le_upper l x (l x) le_rfl)
  refine Finset.sup_le (fun z hz => ?_)
  exact hrefl z x (Finset.mem_filter.mp hz).2

end

-- [D-1440] exists_epPartner
theorem exists_epPartner (l : α → β) (hbot : l ⊥ = ⊥)
    (hsup : ∀ a b, l (a ⊔ b) = l a ⊔ l b) (hrefl : ∀ a b : α, l a ≤ l b → a ≤ b) :
    ∃ u : β → α, Monotone u ∧ (∀ x, u (l x) = x) ∧ (∀ y, l (u y) ≤ y) :=
  ⟨upper l, upper_monotone l hbot hsup, upper_map l hsup hrefl, map_upper_le l hbot hsup⟩

end EpFromJoin
