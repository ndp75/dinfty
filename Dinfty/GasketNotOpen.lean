import Dinfty.GasketCoreIFS

-- [D-2754] §TheoremAData-quotient-map-asks-for-something
open Metric Set Filter Topology

namespace Gasket

-- [D-2755] §1-Coordinates-on-the-gasket
-- [D-2756] fst_le_one
theorem fst_le_one {q : E} (hq : q ∈ gasketSet) : q.1 ≤ 1 := by
  have h := gasketSet_subset_closedBall hq
  rw [mem_closedBall, Prod.dist_eq] at h
  have h1 : dist q.1 vA.1 ≤ 1 := le_trans (le_max_left _ _) h
  rw [Real.dist_eq] at h1
  have h2 : |q.1 - vA.1| ≤ 1 := h1
  have h3 : q.1 - vA.1 ≤ 1 := (abs_le.1 h2).2
  simpa [vA] using h3

-- [D-2757] contract_cA_fst
theorem contract_cA_fst (q : E) : (contract cA q).1 = 2⁻¹ * q.1 := by
  simp [contract, cA]

-- [D-2758] contract_cB_fst
theorem contract_cB_fst (q : E) : (contract cB q).1 = 2⁻¹ * q.1 + 2⁻¹ := by
  simp [contract, cB]

-- [D-2759] fst_le_half_of_mem_imageA
theorem fst_le_half_of_mem_imageA {p : E} (hp : p ∈ contract cA '' gasketSet) :
    p.1 ≤ 2⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [contract_cA_fst]
  have := fst_le_one hq
  linarith

-- [D-2760] §2-The-contact-point-and-points-of-approaching
-- [D-2761] mid
noncomputable def mid : E := contract cA vB

-- [D-2762] mid_mem_imageA
theorem mid_mem_imageA : mid ∈ contract cA '' gasketSet := ⟨vB, vB_mem, rfl⟩

-- [D-2763] mid_mem
theorem mid_mem : mid ∈ gasketSet := mapsTo_cA vB_mem

-- [D-2764] mid_eq
theorem mid_eq : mid = ((2⁻¹ : ℝ), (0 : ℝ)) := by
  simp [mid, contract, cA, vB, Prod.ext_iff]

-- [D-2765] qq
noncomputable def qq (n : ℕ) : E := (contract cA)^[n] vB

-- [D-2766] qq_mem
theorem qq_mem (n : ℕ) : qq n ∈ gasketSet := mapsTo_cA.iterate n vB_mem

-- [D-2767] qq_eq
theorem qq_eq (n : ℕ) : qq n = (((2⁻¹ : ℝ) ^ n), (0 : ℝ)) := by
  induction n with
  | zero => simp [qq, vB]
  | succ n ih =>
      rw [qq, Function.iterate_succ_apply']
      show contract cA (qq n) = _
      rw [ih]
      simp [contract, cA, Prod.ext_iff, pow_succ]
      ring

-- [D-2768] pp
noncomputable def pp (n : ℕ) : E := contract cB (qq n)

-- [D-2769] pp_mem
theorem pp_mem (n : ℕ) : pp n ∈ gasketSet := mapsTo_cB (qq_mem n)

-- [D-2770] pp_eq
theorem pp_eq (n : ℕ) : pp n = ((2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n + 2⁻¹, (0 : ℝ)) := by
  rw [pp, qq_eq]
  simp [contract, cB, Prod.ext_iff]

-- [D-2771] pp_not_mem_imageA
theorem pp_not_mem_imageA (n : ℕ) : pp n ∉ contract cA '' gasketSet := by
  intro h
  have h1 := fst_le_half_of_mem_imageA h
  rw [pp_eq] at h1
  have h2 : (0:ℝ) < (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n := by positivity
  simp only at h1
  linarith

-- [D-2772] dist_pp_mid
theorem dist_pp_mid (n : ℕ) : dist (pp n) mid = (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n := by
  rw [pp_eq, mid_eq, Prod.dist_eq]
  have h2 : (0:ℝ) ≤ (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n := by positivity
  simp [Real.dist_eq, abs_of_nonneg h2]

-- [D-2773] §3-The-A-copy-is-not-open
-- [D-2774] not_isOpen_imageA
theorem not_isOpen_imageA :
    ¬ IsOpen {x : Gamma | (x : E) ∈ contract cA '' gasketSet} := by
  intro hopen
  have hmem : (⟨mid, mid_mem⟩ : Gamma) ∈ {x : Gamma | (x : E) ∈ contract cA '' gasketSet} :=
    mid_mem_imageA
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n < ε := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    have h2 : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using h.const_mul (2⁻¹ : ℝ)
    exact ((h2.eventually (gt_mem_nhds hε)).exists)
  have hin : (⟨pp n, pp_mem n⟩ : Gamma) ∈ Metric.ball (⟨mid, mid_mem⟩ : Gamma) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    show dist (pp n) mid < ε
    rw [dist_pp_mid]
    exact hn
  exact pp_not_mem_imageA n (hball hin)

-- [D-2775] §4-hence-is-not-an-open-map
-- [D-2776] image_cylinder
theorem image_cylinder :
    codeGamma '' {w : ℕ → Fin 3 | w 0 = 0}
      = {x : Gamma | (x : E) ∈ contract cA '' gasketSet} := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hcons : cons 0 (tail w) = w := by
      have := cons_head_tail w
      rwa [hw] at this
    have hval : codeGamma w = fA (codeGamma (tail w)) := by
      conv_lhs => rw [← hcons]
      exact codeGamma_cons_zero (tail w)
    rw [hval]
    exact ⟨coding (tail w), coding_mem (tail w), rfl⟩
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨w, hw⟩ := coding_surjOn q hq
    refine ⟨cons 0 w, rfl, ?_⟩
    refine Subtype.ext ?_
    rw [codeGamma_cons_zero]
    show contract cA (coding w) = (x : E)
    rw [hw, hqx]

-- [D-2777] isOpen_cylinder
theorem isOpen_cylinder : IsOpen {w : ℕ → Fin 3 | w 0 = 0} := by
  have h : {w : ℕ → Fin 3 | w 0 = 0} = (fun w : ℕ → Fin 3 => w 0) ⁻¹' {0} := rfl
  rw [h]
  exact IsOpen.preimage (continuous_apply 0) (isOpen_discrete _)

-- [D-2778] notOpen
theorem notOpen : ¬ IsOpenMap codeGamma := by
  intro h
  exact not_isOpen_imageA (image_cylinder ▸ h _ isOpen_cylinder)

end Gasket
