import Dinfty.GasketCoding
import Dinfty.CoreIFS

/-!
# The address space as a `CoreIFS` over the real `Γ`

With `Γ` now a definition rather than a parameter, the degenerate reading of the
framework (`Γ := B`, `f_j := σ_j`, `ρ := id`) no longer typechecks: `f_A/f_B/f_C`
are pinned to the three Euclidean contractions.  This module instantiates the
`CoreIFS` *data* at the honest `Γ`, with the address space as carrier, and
proves what `TheoremAData` asks — with one exception, which is the point of the
file.

## Two things a reader must be told

**1.  `Dinf` is a phantom parameter of `CoreIFS`.**  Look at the fields: `Core`,
`topCore`, `sigmaA/B/C`, `fA/fB/fC`.  `Dinf` occurs in none of them.  So a term
of type `CoreIFS B Γ` says *nothing whatever* about `B`, and building one is not
evidence that the tower has been connected to the gasket.  The instance below is
`CoreIFS Empty Γ` precisely so that it cannot be misread as such evidence.

**2.  `TheoremAData.quotient_map` asks for `IsOpenMap ρ`, and for the gasket
that is false.**  This is proved in `Dinfty/GasketNotOpen.lean`
(`Gasket.notOpen : ¬ IsOpenMap codeGamma`), not merely argued: the image of the
open cylinder `{w | w 0 = A}` is the sub-gasket `h_A(Γ)`, and the contact point
`(1/2, 0)` is a limit of points `h_B(h_A^[n] v_B)` of `Γ` lying strictly to its
right, so `h_A(Γ)` is not a neighbourhood of it.

What is true — and what the note presumably meant by "quotient map" — is
`IsQuotientMap`: a continuous surjection from a compact space to a Hausdorff
space is closed, hence a quotient map.  That is `isQuotientMap_codeGamma`
below.  **`TheoremAData` is therefore not instantiated here, and the `IsOpenMap`
field should be replaced by `IsQuotientMap` before it can be.**

## What is proved

* `coding_unique` — **any** map `(ℕ → Fin 3) → Γ` equivariant for the three
  `cons`/`f` pairs is `π`.  No continuity hypothesis is needed: equivariance
  alone pins the value, because the prefix maps contract.  This is strictly
  stronger than `TheoremAData.unique`.
* `isQuotientMap_codeGamma` — the corrected `quotient_map` field.
* `addressCoreIFS` — the `CoreIFS` data.
-/

open Metric Set Filter Topology

namespace Gasket

/-! ## 1.  The shift -/

def tail (w : ℕ → Fin 3) : ℕ → Fin 3 := fun n => w (n + 1)

theorem tail_iterate (n : ℕ) (w : ℕ → Fin 3) (k : ℕ) :
    (tail^[n] w) k = w (n + k) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      show w (n + k + 1) = w (n + 1 + k)
      congr 1
      omega

theorem cons_head_tail (w : ℕ → Fin 3) : cons (w 0) (tail w) = w := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ## 2.  Equivariance pins the map — with no continuity hypothesis -/

section Unique

variable (r : (ℕ → Fin 3) → Gamma)
  (hA : ∀ w, r (cons 0 w) = fA (r w))
  (hB : ∀ w, r (cons 1 w) = fB (r w))
  (hC : ∀ w, r (cons 2 w) = fC (r w))

include hA hB hC

theorem step_head (w : ℕ → Fin 3) :
    step (w 0) ((r (tail w) : Gamma) : E) = ((r w : Gamma) : E) := by
  have hw : r w = r (cons (w 0) (tail w)) := by rw [cons_head_tail]
  have hsplit : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases hsplit (w 0) with h | h | h
  · rw [h] at hw ⊢; rw [hw, hA]; simp [step, cw, fA]
  · rw [h] at hw ⊢; rw [hw, hB]; simp [step, cw, fB]
  · rw [h] at hw ⊢; rw [hw, hC]; simp [step, cw, fC]

theorem pre_iterate_eq (w : ℕ → Fin 3) (n : ℕ) :
    pre w n ((r (tail^[n] w) : Gamma) : E) = ((r w : Gamma) : E) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [pre_succ]
      show pre w n (step (w n) ((r (tail^[n + 1] w) : Gamma) : E)) = _
      have hshift : tail^[n + 1] w = tail (tail^[n] w) := Function.iterate_succ_apply' tail n w
      have hhead : (tail^[n] w) 0 = w n := by rw [tail_iterate]; simp
      rw [hshift, ← hhead, step_head r hA hB hC (tail^[n] w), ih]

/-- **Equivariance alone determines the coding map.** -/
theorem coding_unique : r = codeGamma := by
  obtain ⟨M, hM⟩ := isCompact_gasketSet.isBounded.subset_closedBall vA
  funext w
  refine Subtype.ext ?_
  have hclose : ∀ n, dist (xseq w n) ((r w : Gamma) : E) ≤ (2⁻¹ : ℝ) ^ n * M := by
    intro n
    have h1 : dist (xseq w n) ((r w : Gamma) : E)
        = dist (pre w n vA) (pre w n ((r (tail^[n] w) : Gamma) : E)) := by
      rw [pre_iterate_eq r hA hB hC w n]
      rfl
    rw [h1]
    have h2 := (pre_lipschitz w n).dist_le_mul vA ((r (tail^[n] w) : Gamma) : E)
    have h3 : ((((2⁻¹ : NNReal)) ^ n : NNReal) : ℝ) = (2⁻¹ : ℝ) ^ n := by
      push_cast; norm_num
    rw [h3] at h2
    refine h2.trans ?_
    have h4 : (0:ℝ) ≤ (2⁻¹ : ℝ) ^ n := by positivity
    exact mul_le_mul_of_nonneg_left (mem_closedBall'.1 (hM (r (tail^[n] w)).2)) h4
  have htend : Tendsto (xseq w) atTop (𝓝 ((r w : Gamma) : E)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) hclose ?_
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    simpa using h.mul_const M
  exact tendsto_nhds_unique htend (coding_tendsto w)

end Unique

/-! ## 3.  `π` is a quotient map — but not an open one -/

instance : CompactSpace (ℕ → Fin 3) := Pi.compactSpace

theorem isClosedMap_codeGamma : IsClosedMap codeGamma :=
  continuous_codeGamma.isClosedMap

/-- The corrected `quotient_map` field: `π` is a quotient map.  It is **not** an
open map — see the module docstring. -/
theorem isQuotientMap_codeGamma : IsQuotientMap codeGamma :=
  isClosedMap_codeGamma.isQuotientMap continuous_codeGamma codeGamma_surjective

/-! ## 4.  The `CoreIFS` data

`Dinf` is instantiated at `Empty` on purpose: it is a phantom parameter, and
nothing here connects the gasket to `D∞`. -/

noncomputable def addressCoreIFS : CoreIFS Empty Gamma where
  Core := ℕ → Fin 3
  topCore := inferInstance
  sigmaA := cons 0
  sigmaB := cons 1
  sigmaC := cons 2
  fA := fA
  fB := fB
  fC := fC

theorem addressCoreIFS_equivariant :
    (∀ w, codeGamma (addressCoreIFS.sigmaA w) = addressCoreIFS.fA (codeGamma w)) ∧
    (∀ w, codeGamma (addressCoreIFS.sigmaB w) = addressCoreIFS.fB (codeGamma w)) ∧
    (∀ w, codeGamma (addressCoreIFS.sigmaC w) = addressCoreIFS.fC (codeGamma w)) :=
  ⟨codeGamma_cons_zero, codeGamma_cons_one, codeGamma_cons_two⟩

theorem addressCoreIFS_unique (r : (ℕ → Fin 3) → Gamma)
    (hA : ∀ w, r (addressCoreIFS.sigmaA w) = addressCoreIFS.fA (r w))
    (hB : ∀ w, r (addressCoreIFS.sigmaB w) = addressCoreIFS.fB (r w))
    (hC : ∀ w, r (addressCoreIFS.sigmaC w) = addressCoreIFS.fC (r w)) :
    r = codeGamma :=
  coding_unique r hA hB hC

end Gasket
