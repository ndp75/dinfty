import Dinfty.CodeB

open GluingTowerLibrary SierpinskiApplication

-- [D-2881] §What-continuous-can-mean
open Set Filter Topology

namespace RhoContinuity

open PhiIterateTower PhiBilimit SigmaRebuild CodeB

-- [D-2882] §1-is-in-the-attractor-and-sends
-- [D-2883] codeGamma_constA
theorem codeGamma_constA : Gasket.codeGamma (fun _ => 0) = Gasket.gA := by
  refine Gasket.fA_fixed_unique ?_
  have h : Gasket.cons 0 (fun _ => (0 : Fin 3)) = (fun _ => (0 : Fin 3)) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => rfl
  have h2 := Gasket.codeGamma_cons_zero (fun _ => (0 : Fin 3))
  rw [h] at h2
  exact h2.symm

-- [D-2884] rho_bot_eq
theorem rho_bot_eq : rho ⟨(⊥ : B), bot_mem_attractor⟩ = Gasket.gA := by
  have h1 : (⟨(⊥ : B), bot_mem_attractor⟩ : Attractor)
      = ⟨codeB (fun _ => 0), codeB_mem_attractor _⟩ := Subtype.ext codeB_constA.symm
  rw [h1, rho_codeB]
  exact codeGamma_constA

-- [D-2885] §2-No-topology-with-upward-closed-opens-can-work
-- [D-2886] UpwardClosedOpens
def UpwardClosedOpens (τ : TopologicalSpace Attractor) : Prop :=
  ∀ U : Set Attractor, IsOpen[τ] U → ∀ a ∈ U, ∀ b : Attractor, (a : B) ≤ (b : B) → b ∈ U

-- [D-2887] no_continuous_rho_of_upwardClosed
theorem no_continuous_rho_of_upwardClosed (τ : TopologicalSpace Attractor)
    (hup : UpwardClosedOpens τ) (hcont : Continuous[τ, _] rho) : False := by
  have hopen : IsOpen[τ] (rho ⁻¹' {Gasket.gB}ᶜ) :=
    hcont.isOpen_preimage _ (isClosed_singleton (x := Gasket.gB)).isOpen_compl
  have hbot : (⟨(⊥ : B), bot_mem_attractor⟩ : Attractor) ∈ rho ⁻¹' {Gasket.gB}ᶜ := by
    show rho ⟨(⊥ : B), bot_mem_attractor⟩ ∉ ({Gasket.gB} : Set Gasket.Gamma)
    rw [rho_bot_eq]
    exact fun hc => Gasket.gA_ne_gB hc
  obtain ⟨a, ha⟩ := rho_surjective Gasket.gB
  have hmem : a ∈ rho ⁻¹' {Gasket.gB}ᶜ :=
    hup _ hopen _ hbot a bot_le
  exact hmem ha

-- [D-2888] §3-The-notion-this-development-actually-supplies
-- [D-2889] ChainContinuous
def ChainContinuous (f : Attractor → Gasket.Gamma) : Prop :=
  ∀ (x : ℕ → Attractor), Monotone (fun n => ((x n : B)))
    → ∀ c : Attractor, IsLUB (Set.range fun n => ((x n : B))) (c : B)
    → Tendsto (fun n => f (x n)) atTop (𝓝 (f c))

-- [D-2890] AddressesConverge
def AddressesConverge : Prop :=
  ∀ (w : ℕ → (ℕ → Fin 3)) (v : ℕ → Fin 3),
    Monotone (fun n => codeB (w n))
    → IsLUB (Set.range fun n => codeB (w n)) (codeB v)
    → ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ i, i < k → (w n) i = v i

-- [D-2891] §4-The-reduction
-- [D-2892] dist_rho_le_of_prefix
theorem dist_rho_le_of_prefix {u v : ℕ → Fin 3} {k : ℕ} (h : ∀ i, i < k → u i = v i) :
    dist (rho ⟨codeB u, codeB_mem_attractor u⟩) (rho ⟨codeB v, codeB_mem_attractor v⟩)
      ≤ 2 * (2⁻¹ : ℝ) ^ k := by
  rw [rho_codeB, rho_codeB]
  show dist (Gasket.coding u) (Gasket.coding v) ≤ _
  exact Gasket.dist_coding_le_of_prefix (fun i hi => h i hi)

-- [D-2893] chainContinuous_of_addressesConverge
theorem chainContinuous_of_addressesConverge (h : AddressesConverge) :
    ChainContinuous rho := by
  intro x hmono c hc
  obtain ⟨v, hv⟩ := c.2
  have hxaddr : ∀ n, ∃ u, codeB u = (x n : B) := fun n => (x n).2
  choose w hw using hxaddr
  have hmono' : Monotone (fun n => codeB (w n)) := by
    intro a b hab
    show codeB (w a) ≤ codeB (w b)
    rw [hw a, hw b]
    exact hmono hab
  have hc' : IsLUB (Set.range fun n => codeB (w n)) (codeB v) := by
    have hset : (Set.range fun n => codeB (w n)) = Set.range fun n => ((x n : B)) := by
      ext z
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, (hw n).symm.trans hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, (hw n).trans hn⟩
    rw [hset, hv]
    exact hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * (2⁻¹ : ℝ) ^ k < ε := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    have h2 : Tendsto (fun n : ℕ => 2 * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using hpow.const_mul 2
    exact ((h2.eventually (gt_mem_nhds hε)).exists)
  obtain ⟨N, hN⟩ := h w v hmono' hc' k
  refine ⟨N, fun n hn => ?_⟩
  have hxn : x n = ⟨codeB (w n), codeB_mem_attractor (w n)⟩ := Subtype.ext (hw n).symm
  have hcv : c = ⟨codeB v, codeB_mem_attractor v⟩ := Subtype.ext hv.symm
  rw [hxn, hcv]
  exact lt_of_le_of_lt (dist_rho_le_of_prefix (hN n hn)) hk

end RhoContinuity
