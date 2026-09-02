import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

/-!
# The residue is a *definability* statement — and that is why the reductions circle

Eighteen sections of this thread have each ended by asking for an
order-theoretic property that picks out a distinguished element, and each has
handed the question back in new coordinates.  The reason is not that the
reductions were bad.  It is that **"our description is complete" and "the point
is fixed by every automorphism" are the same statement**, so every reduction
that preserves the meaning returns to the same place.

This module proves that, and it is the natural terminus.

## The equivalence

```lean
def OrderInvariant (φ : DInfty → Prop) : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (z : DInfty), φ z → φ (θ z)

def Pins (φ : DInfty → Prop) (z : DInfty) : Prop := ∀ w, φ w ↔ w = z

invariant_pin_iff_fixed :
  (∃ φ, OrderInvariant φ ∧ Pins φ z) ↔ ∀ θ : DInfty ≃o DInfty, θ z = z
```

So `TwoPointFixed` is *exactly* "there is a complete order-theoretic description
of the seam, and one of the stage-`0` top" (`twoPointFixed_iff_pinned`).  There
is no gap between *finding a separator* and *proving the hypothesis* — they are
one statement, and no further reformulation can make one easier than the other.

## What that settles, and the one thing Lean genuinely cannot say

**Settles:** the search is not heuristic.  Either an automorphism-invariant
property pinning `midInf` exists — in which case pillar B's base case is closed —
or one does not, in which case some automorphism moves `midInf` and pillar B is
refuted.  Nothing else is possible, and no cleverer formulation is waiting to be
found.  The remaining work is mathematics, not bookkeeping.

**Cannot say:** note that `φ := (· = midInf)` is invariant *precisely when*
`midInf` is fixed (`eq_pin_invariant_iff`).  So the existential above is not a
search hint on its own — a useful `φ` must be one written **without mentioning
`midInf`**, and "written without mentioning" is a statement about *syntax*, not
about the structure.  Lean can quantify over predicates; it cannot quantify over
*formulas of the order language* without an explicit encoding of that language.

That is the real shape of what this thread kept running into: the completeness
of a description is expressible internally only up to automorphism, and up to
automorphism it is the target itself.  Making it more than that would mean
formalizing the order language and its satisfaction relation — a genuinely
different project, and a large one.

**So the honest terminus is:** the reductions are finished; the statement is as
sharp as an internal formalization allows; what remains is to decide
`TwoPointFixed` mathematically, with §18's poset-algebra question as the live
lead.
-/

open scoped Classical

namespace Definability

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

/-- A property is *order-theoretic* exactly when every order-automorphism
preserves it.  This is the strongest sense of "expressible in the order
language" that is available inside the theory. -/
def OrderInvariant (φ : DInfty → Prop) : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (z : DInfty), φ z → φ (θ z)

/-- `φ` *pins* `z`: it holds of `z` and of nothing else — a complete
description. -/
def Pins (φ : DInfty → Prop) (z : DInfty) : Prop := ∀ w, φ w ↔ w = z

/-- **The completeness theorem.**  A complete order-theoretic description of `z`
exists if and only if `z` is fixed by every automorphism.  "Our description is
complete" and "the point does not move" are one statement. -/
theorem invariant_pin_iff_fixed (z : DInfty) :
    (∃ φ, OrderInvariant φ ∧ Pins φ z) ↔ ∀ θ : DInfty ≃o DInfty, θ z = z := by
  constructor
  · rintro ⟨φ, hinv, hpin⟩ θ
    have hz : φ z := (hpin z).mpr rfl
    exact (hpin (θ z)).mp (hinv θ z hz)
  · intro h
    refine ⟨fun w => w = z, ?_, ?_⟩
    · intro θ w hw
      rw [hw]; exact h θ
    · intro w; exact Iff.rfl

/-- The caveat, made explicit: the *trivial* description `(· = z)` is invariant
precisely when `z` is fixed.  So the existential above carries no search
information by itself — a useful `φ` is one written without naming `z`, and that
is a condition on syntax, which the theory cannot state about itself. -/
theorem eq_pin_invariant_iff (z : DInfty) :
    OrderInvariant (fun w => w = z) ↔ ∀ θ : DInfty ≃o DInfty, θ z = z := by
  constructor
  · intro h θ; exact h θ z rfl
  · intro h θ w hw; rw [hw]; exact h θ

/-- **`TwoPointFixed` restated as completeness of two descriptions.**  This is
the terminus of the reduction chain: no further reformulation can separate
"find the separator" from "prove the hypothesis". -/
theorem twoPointFixed_iff_pinned :
    TwoPointFixed ↔
      ((∃ φ, OrderInvariant φ ∧ Pins φ midInf) ∧
       (∃ ψ, OrderInvariant ψ ∧ Pins ψ (toD 0 (⊤ : D 0)))) := by
  constructor
  · intro h
    exact ⟨(invariant_pin_iff_fixed midInf).mpr (fun θ => (h θ).1),
           (invariant_pin_iff_fixed (toD 0 (⊤ : D 0))).mpr (fun θ => (h θ).2)⟩
  · rintro ⟨h1, h2⟩ θ
    exact ⟨(invariant_pin_iff_fixed midInf).mp h1 θ,
           (invariant_pin_iff_fixed (toD 0 (⊤ : D 0))).mp h2 θ⟩

/-- And the dichotomy, spelled out.  Exactly one of these holds, and nothing
else is available. -/
theorem completeness_dichotomy :
    (∃ φ, OrderInvariant φ ∧ Pins φ midInf) ∨ (∃ θ : DInfty ≃o DInfty, θ midInf ≠ midInf) := by
  by_cases h : ∀ θ : DInfty ≃o DInfty, θ midInf = midInf
  · exact Or.inl ((invariant_pin_iff_fixed midInf).mpr h)
  · push_neg at h
    exact Or.inr h

end Definability
