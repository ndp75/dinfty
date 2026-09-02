import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Module.Basic

-- [D-2621] §the-Sierpi-ski-gasket-as-an-actual-attractor
open Metric EMetric Set TopologicalSpace

namespace Gasket

-- [D-2622] §1-A-Lipschitz-map-is-Lipschitz-on-nonempty
section LipHaus

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {K : NNReal} {f : α → β}

-- [D-2623] infEDist_image_le
theorem infEDist_image_le (hf : LipschitzWith K f) (x : α) {t : Set α} (ht : t.Nonempty) :
    infEDist (f x) (f '' t) ≤ K * infEDist x t := by
  rcases eq_or_ne K 0 with rfl | hK
  · obtain ⟨y, hy⟩ := ht
    have h0 : edist (f x) (f y) ≤ 0 := by simpa using hf x y
    have h1 : infEDist (f x) (f '' t) ≤ edist (f x) (f y) :=
      infEDist_le_edist_of_mem (mem_image_of_mem f hy)
    simpa using h1.trans h0
  · have hKtop : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hK0 : (K : ENNReal) ≠ 0 := by simpa using hK
    have himg : infEDist (f x) (f '' t) = ⨅ y ∈ t, edist (f x) (f y) := by
      simp only [infEDist, iInf_image]
    rw [himg, infEDist]
    simp only [ENNReal.mul_iInf_of_ne hK0 hKtop]
    exact iInf₂_mono fun y _ => hf x y

-- [D-2624] hausdorffEDist_image_le
theorem hausdorffEDist_image_le (hf : LipschitzWith K f) {s t : Set α}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEDist (f '' s) (f '' t) ≤ K * hausdorffEDist s t := by
  refine hausdorffEDist_le_of_infEDist ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine (infEDist_image_le hf x ht).trans ?_
    gcongr
    exact infEDist_le_hausdorffEDist_of_mem hx
  · rintro _ ⟨y, hy, rfl⟩
    refine (infEDist_image_le hf y hs).trans ?_
    gcongr
    rw [hausdorffEDist_comm]
    exact infEDist_le_hausdorffEDist_of_mem hy

-- [D-2625] lipschitzWith_map
theorem lipschitzWith_map (hf : LipschitzWith K f) :
    LipschitzWith K (fun S : NonemptyCompacts α => S.map f hf.continuous) := by
  intro S T
  exact hausdorffEDist_image_le hf S.nonempty T.nonempty

end LipHaus

-- [D-2626] §2-The-three-contractions
-- [D-2627] E
abbrev E : Type := ℝ × ℝ

-- [D-2628] cA
def cA : E := (0, 0)
-- [D-2629] cB
noncomputable def cB : E := (2⁻¹, 0)
-- [D-2630] cC
noncomputable def cC : E := (0, 2⁻¹)

-- [D-2631] vA
def vA : E := (0, 0)
-- [D-2632] vB
def vB : E := (1, 0)
-- [D-2633] vC
def vC : E := (0, 1)

-- [D-2634] contract
noncomputable def contract (c : E) (p : E) : E := (2 : ℝ)⁻¹ • p + c

-- [D-2635] contract_lipschitz
theorem contract_lipschitz (c : E) : LipschitzWith (2⁻¹ : NNReal) (contract c) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h : dist (contract c p) (contract c q) = dist ((2:ℝ)⁻¹ • p) ((2:ℝ)⁻¹ • q) := by
    simp [contract, dist_add_right]
  rw [h, dist_smul₀]
  norm_num

-- [D-2636] contract_continuous
theorem contract_continuous (c : E) : Continuous (contract c) :=
  (contract_lipschitz c).continuous

-- [D-2637] contract_vA
@[simp] theorem contract_vA : contract cA vA = vA := by
  simp [contract, cA, vA, Prod.ext_iff]

-- [D-2638] contract_vB
@[simp] theorem contract_vB : contract cB vB = vB := by
  simp [contract, cB, vB, Prod.ext_iff]
  norm_num

-- [D-2639] contract_vC
@[simp] theorem contract_vC : contract cC vC = vC := by
  simp [contract, cC, vC, Prod.ext_iff]
  norm_num

-- [D-2640] §3-The-Hutchinson-operator-and-its-fixed-point
-- [D-2641] hutch
noncomputable def hutch (S : NonemptyCompacts E) : NonemptyCompacts E :=
  (S.map (contract cA) (contract_continuous _)) ⊔
  (S.map (contract cB) (contract_continuous _)) ⊔
  (S.map (contract cC) (contract_continuous _))

-- [D-2642] coe_hutch
theorem coe_hutch (S : NonemptyCompacts E) :
    (hutch S : Set E) =
      (contract cA '' S) ∪ (contract cB '' S) ∪ (contract cC '' S) := by
  simp [hutch]

-- [D-2643] hutch_lipschitz
theorem hutch_lipschitz : LipschitzWith (2⁻¹ : NNReal) hutch := by
  intro S T
  have hA := lipschitzWith_map (contract_lipschitz cA) S T
  have hB := lipschitzWith_map (contract_lipschitz cB) S T
  have hC := lipschitzWith_map (contract_lipschitz cC) S T
  have hstep : edist (hutch S) (hutch T)
      ≤ max (max (edist (S.map (contract cA) (contract_continuous _))
                        (T.map (contract cA) (contract_continuous _)))
                 (edist (S.map (contract cB) (contract_continuous _))
                        (T.map (contract cB) (contract_continuous _))))
            (edist (S.map (contract cC) (contract_continuous _))
                   (T.map (contract cC) (contract_continuous _))) := by
    show hausdorffEDist ((hutch S : Set E)) ((hutch T : Set E)) ≤ _
    rw [coe_hutch, coe_hutch]
    exact le_trans hausdorffEDist_union_le
      (max_le_max hausdorffEDist_union_le (le_refl _))
  exact hstep.trans (max_le (max_le hA hB) hC)

-- [D-2644] hutch_contracting
theorem hutch_contracting : ContractingWith (2⁻¹ : NNReal) hutch :=
  ⟨by norm_num, hutch_lipschitz⟩

-- [D-2645] edist_ne_top
theorem edist_ne_top (S T : NonemptyCompacts E) : edist S T ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded S.nonempty T.nonempty
    S.isCompact.isBounded T.isCompact.isBounded

-- [D-2646] gasketNC
noncomputable def gasketNC : NonemptyCompacts E :=
  ContractingWith.efixedPoint hutch hutch_contracting {vA} (edist_ne_top _ _)

-- [D-2647] hutch_gasketNC
theorem hutch_gasketNC : hutch gasketNC = gasketNC :=
  ContractingWith.efixedPoint_isFixedPt hutch_contracting _

-- [D-2648] gasketSet
def gasketSet : Set E := (gasketNC : Set E)

-- [D-2649] gasketSet_nonempty
theorem gasketSet_nonempty : gasketSet.Nonempty := gasketNC.nonempty

-- [D-2650] isCompact_gasketSet
theorem isCompact_gasketSet : IsCompact gasketSet := gasketNC.isCompact

-- [D-2651] gasketSet_eq
theorem gasketSet_eq :
    gasketSet = (contract cA '' gasketSet) ∪ (contract cB '' gasketSet)
      ∪ (contract cC '' gasketSet) := by
  conv_lhs => rw [gasketSet, ← hutch_gasketNC]
  rw [coe_hutch]
  rfl

-- [D-2652] mapsTo_cA
theorem mapsTo_cA : MapsTo (contract cA) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inl (Or.inl ⟨x, hx, rfl⟩)

-- [D-2653] mapsTo_cB
theorem mapsTo_cB : MapsTo (contract cB) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inl (Or.inr ⟨x, hx, rfl⟩)

-- [D-2654] mapsTo_cC
theorem mapsTo_cC : MapsTo (contract cC) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inr ⟨x, hx, rfl⟩

-- [D-2655] §4-as-a-compact-metric-space-with-its-three-maps
-- [D-2656] Gamma
abbrev Gamma : Type := gasketSet

-- [D-2657] inst-CompactSpace
instance : CompactSpace Gamma := isCompact_iff_compactSpace.mp isCompact_gasketSet

-- [D-2658] inst-Nonempty
instance : Nonempty Gamma := gasketSet_nonempty.to_subtype

-- [D-2659] fA
noncomputable def fA : Gamma → Gamma := fun x => ⟨contract cA x, mapsTo_cA x.2⟩
-- [D-2660] fB
noncomputable def fB : Gamma → Gamma := fun x => ⟨contract cB x, mapsTo_cB x.2⟩
-- [D-2661] fC
noncomputable def fC : Gamma → Gamma := fun x => ⟨contract cC x, mapsTo_cC x.2⟩

-- [D-2662] continuous_fA
theorem continuous_fA : Continuous fA :=
  Continuous.subtype_mk ((contract_continuous cA).comp continuous_subtype_val) _

-- [D-2663] continuous_fB
theorem continuous_fB : Continuous fB :=
  Continuous.subtype_mk ((contract_continuous cB).comp continuous_subtype_val) _

-- [D-2664] continuous_fC
theorem continuous_fC : Continuous fC :=
  Continuous.subtype_mk ((contract_continuous cC).comp continuous_subtype_val) _

-- [D-2665] §5-The-three-vertices-lie-in-and-are-distinct
-- [D-2666] dist_iterate_le
theorem dist_iterate_le (c : E) {v : E} (hv : contract c v = v) (g : E) (n : ℕ) :
    dist ((contract c)^[n] g) v ≤ (2⁻¹ : ℝ) ^ n * dist g v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h1 : dist (contract c ((contract c)^[n] g)) (contract c v)
          ≤ (2⁻¹ : ℝ) * dist ((contract c)^[n] g) v := by
        simpa using (contract_lipschitz c).dist_le_mul ((contract c)^[n] g) v
      rw [hv] at h1
      refine h1.trans ?_
      have h2 : (2⁻¹ : ℝ) * dist ((contract c)^[n] g) v
          ≤ (2⁻¹ : ℝ) * ((2⁻¹ : ℝ) ^ n * dist g v) := by
        have : (0:ℝ) ≤ 2⁻¹ := by norm_num
        exact mul_le_mul_of_nonneg_left ih this
      refine h2.trans_eq ?_
      ring

-- [D-2667] fixedPoint_mem_gasketSet
theorem fixedPoint_mem_gasketSet (c : E) {v : E} (hv : contract c v = v)
    (hmaps : MapsTo (contract c) gasketSet gasketSet) : v ∈ gasketSet := by
  obtain ⟨g, hg⟩ := gasketSet_nonempty
  have hmem : ∀ n, (contract c)^[n] g ∈ gasketSet := fun n => hmaps.iterate n hg
  have hzero : Filter.Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n * dist g v)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    simpa using h.mul_const (dist g v)
  have htend : Filter.Tendsto (fun n : ℕ => (contract c)^[n] g) Filter.atTop (nhds v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => dist_iterate_le c hv g n) hzero
  exact isCompact_gasketSet.isClosed.mem_of_tendsto htend
    (Filter.Eventually.of_forall hmem)

-- [D-2668] vA_mem
theorem vA_mem : vA ∈ gasketSet := fixedPoint_mem_gasketSet cA contract_vA mapsTo_cA
-- [D-2669] vB_mem
theorem vB_mem : vB ∈ gasketSet := fixedPoint_mem_gasketSet cB contract_vB mapsTo_cB
-- [D-2670] vC_mem
theorem vC_mem : vC ∈ gasketSet := fixedPoint_mem_gasketSet cC contract_vC mapsTo_cC

-- [D-2671] vA_ne_vB
theorem vA_ne_vB : vA ≠ vB := by simp [vA, vB, Prod.ext_iff]
-- [D-2672] vA_ne_vC
theorem vA_ne_vC : vA ≠ vC := by simp [vA, vC, Prod.ext_iff]
-- [D-2673] vB_ne_vC
theorem vB_ne_vC : vB ≠ vC := by simp [vB, vC, Prod.ext_iff]

-- [D-2674] §as-points
-- [D-2675] gA
def gA : Gamma := ⟨vA, vA_mem⟩
-- [D-2676] gB
def gB : Gamma := ⟨vB, vB_mem⟩
-- [D-2677] gC
def gC : Gamma := ⟨vC, vC_mem⟩

-- [D-2678] fA_gA
@[simp] theorem fA_gA : fA gA = gA := Subtype.ext contract_vA
-- [D-2679] fB_gB
@[simp] theorem fB_gB : fB gB = gB := Subtype.ext contract_vB
-- [D-2680] fC_gC
@[simp] theorem fC_gC : fC gC = gC := Subtype.ext contract_vC

-- [D-2681] gA_ne_gB
theorem gA_ne_gB : gA ≠ gB := fun h => vA_ne_vB (congrArg Subtype.val h)
-- [D-2682] gA_ne_gC
theorem gA_ne_gC : gA ≠ gC := fun h => vA_ne_vC (congrArg Subtype.val h)
-- [D-2683] gB_ne_gC
theorem gB_ne_gC : gB ≠ gC := fun h => vB_ne_vC (congrArg Subtype.val h)

-- [D-2684] gamma_nontrivial
theorem gamma_nontrivial : Nontrivial Gamma := ⟨⟨gA, gB, gA_ne_gB⟩⟩

end Gasket
