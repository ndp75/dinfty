import Mathlib.Order.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# An order-reflecting, join-preserving map has an ep-partner

Abstract, Mathlib-only.  §79 reduced "does the F-tower's embedding `glueAA k`
have an embedding/projection partner?" to "does it preserve joins?".  This
module is the implication in that reduction, stated for any map of finite
lattices, so that the tower side has only the join question left.

The partner is the usual upper adjoint, `u y = ⨆ {x | l x ≤ y}`, which exists
because the domain is finite:

* `l (u y) ≤ y` — the **deflation** — is exactly join-preservation applied to
  the defining `Finset.sup`;
* `u (l x) = x` — the **retraction** — is order-reflection, which for an
  order embedding is free.

Nothing here is about the tower, and nothing here needs `l` to be monotone as a
hypothesis: join-preservation gives it.
-/

open scoped Classical

namespace EpFromJoin

variable {α β : Type*} [Lattice α] [OrderBot α] [Fintype α] [Lattice β] [OrderBot β]

section

variable (l : α → β) (hbot : l ⊥ = ⊥) (hsup : ∀ a b, l (a ⊔ b) = l a ⊔ l b)

include hsup in
theorem monotone_of_sup : Monotone l := by
  intro a b hab
  have h : l b = l a ⊔ l b := by rw [← hsup a b, sup_eq_right.mpr hab]
  exact h ▸ le_sup_left

include hbot hsup in
/-- Join-preservation upgrades from binary to finite, the domain being finite. -/
theorem map_finset_sup (s : Finset α) : l (s.sup id) = s.sup l := by
  induction s using Finset.induction_on with
  | empty => simpa using hbot
  | @insert a s _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, hsup, ih]
      rfl

/-- The candidate partner: the largest element the map sends below `y`. -/
noncomputable def upper (y : β) : α := (Finset.univ.filter (fun x => l x ≤ y)).sup id

include hbot hsup in
/-- **The deflation half.** -/
theorem map_upper_le (y : β) : l (upper l y) ≤ y := by
  rw [upper, map_finset_sup l hbot hsup]
  refine Finset.sup_le (fun x hx => ?_)
  exact (Finset.mem_filter.mp hx).2

theorem le_upper (x : α) (y : β) (h : l x ≤ y) : x ≤ upper l y :=
  Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)

include hbot hsup in
/-- `l` and `upper l` form a Galois connection. -/
theorem galoisConnection : GaloisConnection l (upper l) := by
  intro x y
  constructor
  · exact le_upper l x y
  · intro h
    exact le_trans (monotone_of_sup l hsup h) (map_upper_le l hbot hsup y)

include hbot hsup in
theorem upper_monotone : Monotone (upper l) := by
  intro y y' hyy'
  exact (galoisConnection l hbot hsup).monotone_u hyy'

include hsup in
/-- **The retraction half**, from order reflection. -/
theorem upper_map (hrefl : ∀ a b : α, l a ≤ l b → a ≤ b) (x : α) : upper l (l x) = x := by
  refine le_antisymm ?_ (le_upper l x (l x) le_rfl)
  refine Finset.sup_le (fun z hz => ?_)
  exact hrefl z x (Finset.mem_filter.mp hz).2

end

/-- **An order-reflecting, join-preserving map of finite lattices has an
embedding/projection partner.** -/
theorem exists_epPartner (l : α → β) (hbot : l ⊥ = ⊥)
    (hsup : ∀ a b, l (a ⊔ b) = l a ⊔ l b) (hrefl : ∀ a b : α, l a ≤ l b → a ≤ b) :
    ∃ u : β → α, Monotone u ∧ (∀ x, u (l x) = x) ∧ (∀ y, l (u y) ≤ y) :=
  ⟨upper l, upper_monotone l hbot hsup, upper_map l hsup hrefl, map_upper_le l hbot hsup⟩

end EpFromJoin
