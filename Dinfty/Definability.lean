import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

-- [D-1725] §The-residue-is-a-definability-statement
open scoped Classical

namespace Definability

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

-- [D-1726] OrderInvariant
def OrderInvariant (φ : DInfty → Prop) : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (z : DInfty), φ z → φ (θ z)

-- [D-1727] Pins
def Pins (φ : DInfty → Prop) (z : DInfty) : Prop := ∀ w, φ w ↔ w = z

-- [D-1728] invariant_pin_iff_fixed
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

-- [D-1729] eq_pin_invariant_iff
theorem eq_pin_invariant_iff (z : DInfty) :
    OrderInvariant (fun w => w = z) ↔ ∀ θ : DInfty ≃o DInfty, θ z = z := by
  constructor
  · intro h θ; exact h θ z rfl
  · intro h θ w hw; rw [hw]; exact h θ

-- [D-1730] twoPointFixed_iff_pinned
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

-- [D-1731] completeness_dichotomy
theorem completeness_dichotomy :
    (∃ φ, OrderInvariant φ ∧ Pins φ midInf) ∨ (∃ θ : DInfty ≃o DInfty, θ midInf ≠ midInf) := by
  by_cases h : ∀ θ : DInfty ≃o DInfty, θ midInf = midInf
  · exact Or.inl ((invariant_pin_iff_fixed midInf).mpr h)
  · push_neg at h
    exact Or.inr h

end Definability
