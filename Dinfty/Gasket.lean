import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Module.Basic

/-!
# `Γ` — the Sierpiński gasket, as an actual attractor

Every previous file in this development that mentions `Γ` treats it as an
abstract parameter.  That is what makes a **degenerate** `CoreIFS` instance
(`Γ := B`, `f_j := σ_j`, `ρ := id`) typecheck while meaning nothing.  This
module removes the parameter: `Γ` is *constructed*, once, as the attractor of
three explicit contractions of `ℝ × ℝ`, and there is nothing left to choose.

The construction is Hutchinson's, and Mathlib supplies almost all of it:

* `TopologicalSpace.NonemptyCompacts E` is a complete `EMetricSpace` under the
  Hausdorff distance (`Topology.MetricSpace.Closeds`);
* `ContractingWith.efixedPoint` is Banach's fixed point theorem.

The one piece Mathlib does **not** have is that a `LipschitzWith K` map is
`LipschitzWith K` on nonempty compacts — it only has the isometry case
(`hausdorffEDist_image`).  §1 supplies it.

The triangle is `(0,0)`, `(1,0)`, `(0,1)` rather than the equilateral one: the
attractor of an affine IFS is affinely equivalent to the equilateral gasket, and
rational vertices keep `√3` out of every subsequent proof.
-/

open Metric EMetric Set TopologicalSpace

namespace Gasket

/-! ## 1.  A Lipschitz map is Lipschitz on nonempty compacts -/

section LipHaus

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {K : NNReal} {f : α → β}

/-- The distance from `f x` to `f '' t` is controlled by `K` times the distance
from `x` to `t`. -/
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

/-- **The Hutchinson estimate.**  Images under a `K`-Lipschitz map are `K`-close
in the Hausdorff distance. -/
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

/-- …stated on `NonemptyCompacts`, where it is a genuine `LipschitzWith`. -/
theorem lipschitzWith_map (hf : LipschitzWith K f) :
    LipschitzWith K (fun S : NonemptyCompacts α => S.map f hf.continuous) := by
  intro S T
  exact hausdorffEDist_image_le hf S.nonempty T.nonempty

end LipHaus

/-! ## 2.  The three contractions -/

/-- The ambient plane.  `ℝ × ℝ` carries the sup metric, which is all that is
used; nothing below depends on the choice. -/
abbrev E : Type := ℝ × ℝ

/-- Translation parts of the three maps.  `contract cJ` fixes the vertex `vJ`. -/
def cA : E := (0, 0)
noncomputable def cB : E := (2⁻¹, 0)
noncomputable def cC : E := (0, 2⁻¹)

def vA : E := (0, 0)
def vB : E := (1, 0)
def vC : E := (0, 1)

/-- `p ↦ p/2 + c`: the generic similarity of ratio `1/2`. -/
noncomputable def contract (c : E) (p : E) : E := (2 : ℝ)⁻¹ • p + c

theorem contract_lipschitz (c : E) : LipschitzWith (2⁻¹ : NNReal) (contract c) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h : dist (contract c p) (contract c q) = dist ((2:ℝ)⁻¹ • p) ((2:ℝ)⁻¹ • q) := by
    simp [contract, dist_add_right]
  rw [h, dist_smul₀]
  norm_num

theorem contract_continuous (c : E) : Continuous (contract c) :=
  (contract_lipschitz c).continuous

@[simp] theorem contract_vA : contract cA vA = vA := by
  simp [contract, cA, vA, Prod.ext_iff]

@[simp] theorem contract_vB : contract cB vB = vB := by
  simp [contract, cB, vB, Prod.ext_iff]
  norm_num

@[simp] theorem contract_vC : contract cC vC = vC := by
  simp [contract, cC, vC, Prod.ext_iff]
  norm_num

/-! ## 3.  The Hutchinson operator and its fixed point -/

/-- `S ↦ h_A(S) ∪ h_B(S) ∪ h_C(S)`, on nonempty compacts. -/
noncomputable def hutch (S : NonemptyCompacts E) : NonemptyCompacts E :=
  (S.map (contract cA) (contract_continuous _)) ⊔
  (S.map (contract cB) (contract_continuous _)) ⊔
  (S.map (contract cC) (contract_continuous _))

theorem coe_hutch (S : NonemptyCompacts E) :
    (hutch S : Set E) =
      (contract cA '' S) ∪ (contract cB '' S) ∪ (contract cC '' S) := by
  simp [hutch]

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

theorem hutch_contracting : ContractingWith (2⁻¹ : NNReal) hutch :=
  ⟨by norm_num, hutch_lipschitz⟩

/-- Two nonempty compacts are at finite Hausdorff distance. -/
theorem edist_ne_top (S T : NonemptyCompacts E) : edist S T ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded S.nonempty T.nonempty
    S.isCompact.isBounded T.isCompact.isBounded

/-- **`Γ`, as a compact set.**  The unique nonempty compact `G` with
`G = h_A(G) ∪ h_B(G) ∪ h_C(G)`. -/
noncomputable def gasketNC : NonemptyCompacts E :=
  ContractingWith.efixedPoint hutch hutch_contracting {vA} (edist_ne_top _ _)

theorem hutch_gasketNC : hutch gasketNC = gasketNC :=
  ContractingWith.efixedPoint_isFixedPt hutch_contracting _

/-- The gasket as a subset of the plane. -/
def gasketSet : Set E := (gasketNC : Set E)

theorem gasketSet_nonempty : gasketSet.Nonempty := gasketNC.nonempty

theorem isCompact_gasketSet : IsCompact gasketSet := gasketNC.isCompact

/-- **The self-similarity identity**, in the plane. -/
theorem gasketSet_eq :
    gasketSet = (contract cA '' gasketSet) ∪ (contract cB '' gasketSet)
      ∪ (contract cC '' gasketSet) := by
  conv_lhs => rw [gasketSet, ← hutch_gasketNC]
  rw [coe_hutch]
  rfl

theorem mapsTo_cA : MapsTo (contract cA) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inl (Or.inl ⟨x, hx, rfl⟩)

theorem mapsTo_cB : MapsTo (contract cB) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inl (Or.inr ⟨x, hx, rfl⟩)

theorem mapsTo_cC : MapsTo (contract cC) gasketSet gasketSet := by
  intro x hx
  rw [gasketSet_eq]
  exact Or.inr ⟨x, hx, rfl⟩

/-! ## 4.  `Γ` as a compact metric space, with its three maps -/

/-- **`Γ`.**  Not a parameter: a definition. -/
abbrev Gamma : Type := gasketSet

instance : CompactSpace Gamma := isCompact_iff_compactSpace.mp isCompact_gasketSet

instance : Nonempty Gamma := gasketSet_nonempty.to_subtype

noncomputable def fA : Gamma → Gamma := fun x => ⟨contract cA x, mapsTo_cA x.2⟩
noncomputable def fB : Gamma → Gamma := fun x => ⟨contract cB x, mapsTo_cB x.2⟩
noncomputable def fC : Gamma → Gamma := fun x => ⟨contract cC x, mapsTo_cC x.2⟩

theorem continuous_fA : Continuous fA :=
  Continuous.subtype_mk ((contract_continuous cA).comp continuous_subtype_val) _

theorem continuous_fB : Continuous fB :=
  Continuous.subtype_mk ((contract_continuous cB).comp continuous_subtype_val) _

theorem continuous_fC : Continuous fC :=
  Continuous.subtype_mk ((contract_continuous cC).comp continuous_subtype_val) _

/-! ## 5.  The three vertices lie in `Γ`, and are distinct

This is the nondegeneracy that makes `Γ` worth having.  Each `contract cJ` fixes
its vertex `vJ`; iterating it from any point of the gasket stays in the gasket
and converges to `vJ`; the gasket is closed.  So `Γ` has at least three points,
and the three IFS maps have three distinct fixed points in it. -/

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

/-- A fixed point of one of the three maps lies in the gasket. -/
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

theorem vA_mem : vA ∈ gasketSet := fixedPoint_mem_gasketSet cA contract_vA mapsTo_cA
theorem vB_mem : vB ∈ gasketSet := fixedPoint_mem_gasketSet cB contract_vB mapsTo_cB
theorem vC_mem : vC ∈ gasketSet := fixedPoint_mem_gasketSet cC contract_vC mapsTo_cC

theorem vA_ne_vB : vA ≠ vB := by simp [vA, vB, Prod.ext_iff]
theorem vA_ne_vC : vA ≠ vC := by simp [vA, vC, Prod.ext_iff]
theorem vB_ne_vC : vB ≠ vC := by simp [vB, vC, Prod.ext_iff]

/-! ### …as points of `Γ` -/

def gA : Gamma := ⟨vA, vA_mem⟩
def gB : Gamma := ⟨vB, vB_mem⟩
def gC : Gamma := ⟨vC, vC_mem⟩

@[simp] theorem fA_gA : fA gA = gA := Subtype.ext contract_vA
@[simp] theorem fB_gB : fB gB = gB := Subtype.ext contract_vB
@[simp] theorem fC_gC : fC gC = gC := Subtype.ext contract_vC

theorem gA_ne_gB : gA ≠ gB := fun h => vA_ne_vB (congrArg Subtype.val h)
theorem gA_ne_gC : gA ≠ gC := fun h => vA_ne_vC (congrArg Subtype.val h)
theorem gB_ne_gC : gB ≠ gC := fun h => vB_ne_vC (congrArg Subtype.val h)

/-- **`Γ` is not a point.**  Three distinct elements, so no degenerate carrier
can be substituted for it. -/
theorem gamma_nontrivial : Nontrivial Gamma := ⟨⟨gA, gB, gA_ne_gB⟩⟩

end Gasket
