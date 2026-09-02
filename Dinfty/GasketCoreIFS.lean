import Dinfty.GasketCoding
import Dinfty.CoreIFS

-- [D-2737] §The-address-space-as-a-CoreIFS-over-the-real
open Metric Set Filter Topology

namespace Gasket

-- [D-2738] §1-The-shift
-- [D-2739] tail
def tail (w : ℕ → Fin 3) : ℕ → Fin 3 := fun n => w (n + 1)

-- [D-2740] tail_iterate
theorem tail_iterate (n : ℕ) (w : ℕ → Fin 3) (k : ℕ) :
    (tail^[n] w) k = w (n + k) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      show w (n + k + 1) = w (n + 1 + k)
      congr 1
      omega

-- [D-2741] cons_head_tail
theorem cons_head_tail (w : ℕ → Fin 3) : cons (w 0) (tail w) = w := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

-- [D-2742] §2-Equivariance-pins-the-map-with-no-continuity
section Unique

variable (r : (ℕ → Fin 3) → Gamma)
  (hA : ∀ w, r (cons 0 w) = fA (r w))
  (hB : ∀ w, r (cons 1 w) = fB (r w))
  (hC : ∀ w, r (cons 2 w) = fC (r w))

include hA hB hC

-- [D-2743] step_head
theorem step_head (w : ℕ → Fin 3) :
    step (w 0) ((r (tail w) : Gamma) : E) = ((r w : Gamma) : E) := by
  have hw : r w = r (cons (w 0) (tail w)) := by rw [cons_head_tail]
  have hsplit : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases hsplit (w 0) with h | h | h
  · rw [h] at hw ⊢; rw [hw, hA]; simp [step, cw, fA]
  · rw [h] at hw ⊢; rw [hw, hB]; simp [step, cw, fB]
  · rw [h] at hw ⊢; rw [hw, hC]; simp [step, cw, fC]

-- [D-2744] pre_iterate_eq
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

-- [D-2745] coding_unique
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

-- [D-2746] §3-is-a-quotient-map-but-not-an-open-one
-- [D-2747] inst-CompactSpace
instance : CompactSpace (ℕ → Fin 3) := Pi.compactSpace

-- [D-2748] isClosedMap_codeGamma
theorem isClosedMap_codeGamma : IsClosedMap codeGamma :=
  continuous_codeGamma.isClosedMap

-- [D-2749] isQuotientMap_codeGamma
theorem isQuotientMap_codeGamma : IsQuotientMap codeGamma :=
  isClosedMap_codeGamma.isQuotientMap continuous_codeGamma codeGamma_surjective

-- [D-2750] §4-The-CoreIFS-data
-- [D-2751] addressCoreIFS
noncomputable def addressCoreIFS : CoreIFS Empty Gamma where
  Core := ℕ → Fin 3
  topCore := inferInstance
  sigmaA := cons 0
  sigmaB := cons 1
  sigmaC := cons 2
  fA := fA
  fB := fB
  fC := fC

-- [D-2752] addressCoreIFS_equivariant
theorem addressCoreIFS_equivariant :
    (∀ w, codeGamma (addressCoreIFS.sigmaA w) = addressCoreIFS.fA (codeGamma w)) ∧
    (∀ w, codeGamma (addressCoreIFS.sigmaB w) = addressCoreIFS.fB (codeGamma w)) ∧
    (∀ w, codeGamma (addressCoreIFS.sigmaC w) = addressCoreIFS.fC (codeGamma w)) :=
  ⟨codeGamma_cons_zero, codeGamma_cons_one, codeGamma_cons_two⟩

-- [D-2753] addressCoreIFS_unique
theorem addressCoreIFS_unique (r : (ℕ → Fin 3) → Gamma)
    (hA : ∀ w, r (addressCoreIFS.sigmaA w) = addressCoreIFS.fA (r w))
    (hB : ∀ w, r (addressCoreIFS.sigmaB w) = addressCoreIFS.fB (r w))
    (hC : ∀ w, r (addressCoreIFS.sigmaC w) = addressCoreIFS.fC (r w)) :
    r = codeGamma :=
  coding_unique r hA hB hC

end Gasket
