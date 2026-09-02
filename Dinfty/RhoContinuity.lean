import Dinfty.CodeB

open GluingTowerLibrary SierpinskiApplication

/-!
# What "continuous" can mean for `ρ`

`TheoremAData` asks for `Continuous rho` against a topology `CoreIFS.topCore`
that the framework leaves free.  This module settles which topologies are
available, and fixes the notion the rest of the development should use.

## 1.  Every order-derived topology is ruled out

The obvious candidate is the Scott topology of `B`, restricted to `𝒦`.  It does
not work, and neither does any other topology built from the order, because they
all share one feature: **their open sets are upward closed**.  That is fatal
here, for a reason that comes from the note's own requirements:

* Theorem ESCAPE says `Fix σ_A = {⊥}`, so in particular `σ_A ⊥ = ⊥`;
* hence `codeB (A,A,A,…) = ⊥`, so **`⊥ ∈ 𝒦`**;
* and `ρ ⊥ = v_A`, because `codeGamma (A,A,A,…)` is a fixed point of `f_A`.

Now `⊥` is below everything, so the only upward-closed set containing it is all
of `𝒦`.  If `ρ` were continuous, the preimage of `Γ ∖ {v_B}` would be an open set
containing `⊥`, hence all of `𝒦`, hence `ρ` would miss `v_B` — contradicting
surjectivity.  That is `no_continuous_rho_of_upwardClosed`.

So the Scott, Alexandrov and upper topologies are all unavailable, and the
failure is not an artefact of the rebuilt `σ`: it follows from `σ_A ⊥ = ⊥`
alone, which Theorem ESCAPE forces.

## 2.  The notion that is left

What the construction actually supplies is suprema of increasing chains — every
theorem in `CodeB` is stated with `IsLUB` — so the notion of continuity native
to this development is:

```lean
ChainContinuous f  :=  every increasing chain in 𝒦 whose supremum lies in 𝒦
                       has `f`-image converging to `f` of the supremum
```

This is sequential Scott-to-metric continuity, and it is *not* refuted by the
argument above: `⊥` sits at the bottom of chains rather than needing small
neighbourhoods.

## 3.  What remains

`ChainContinuous rho` reduces, by the prefix estimate
`Gasket.dist_coding_le_of_prefix`, to a purely combinatorial statement about the
order on `𝒦`: increasing chains have addresses that agree on longer and longer
prefixes with the address of their supremum (`AddressesConverge`).  That
reduction is `chainContinuous_of_addressesConverge`, and `AddressesConverge` is
the one open statement left on the `Γ`/`ρ` side.
-/

open Set Filter Topology

namespace RhoContinuity

open PhiIterateTower PhiBilimit SigmaRebuild CodeB

/-! ## 1.  `⊥` is in the attractor, and `ρ` sends it to the `A`-vertex -/

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

theorem rho_bot_eq : rho ⟨(⊥ : B), bot_mem_attractor⟩ = Gasket.gA := by
  have h1 : (⟨(⊥ : B), bot_mem_attractor⟩ : Attractor)
      = ⟨codeB (fun _ => 0), codeB_mem_attractor _⟩ := Subtype.ext codeB_constA.symm
  rw [h1, rho_codeB]
  exact codeGamma_constA

/-! ## 2.  No topology with upward-closed opens can work -/

/-- The defining feature of every order-derived topology (Scott, Alexandrov,
upper): open sets are upward closed. -/
def UpwardClosedOpens (τ : TopologicalSpace Attractor) : Prop :=
  ∀ U : Set Attractor, IsOpen[τ] U → ∀ a ∈ U, ∀ b : Attractor, (a : B) ≤ (b : B) → b ∈ U

/-- **The refutation.**  With `ρ ⊥ = v_A` and `ρ` surjective, no topology whose
opens are upward closed makes `ρ` continuous. -/
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

/-! ## 3.  The notion this development actually supplies -/

/-- **Chain continuity.**  Increasing chains in `𝒦` whose supremum lies in `𝒦`
have images converging to the image of the supremum.  Every theorem in `CodeB`
is stated with `IsLUB`, so this is the notion native to the construction. -/
def ChainContinuous (f : Attractor → Gasket.Gamma) : Prop :=
  ∀ (x : ℕ → Attractor), Monotone (fun n => ((x n : B)))
    → ∀ c : Attractor, IsLUB (Set.range fun n => ((x n : B))) (c : B)
    → Tendsto (fun n => f (x n)) atTop (𝓝 (f c))

/-- The combinatorial residue: an increasing chain's addresses agree with the
supremum's address on arbitrarily long prefixes. -/
def AddressesConverge : Prop :=
  ∀ (w : ℕ → (ℕ → Fin 3)) (v : ℕ → Fin 3),
    Monotone (fun n => codeB (w n))
    → IsLUB (Set.range fun n => codeB (w n)) (codeB v)
    → ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ i, i < k → (w n) i = v i

/-! ## 4.  The reduction -/

theorem dist_rho_le_of_prefix {u v : ℕ → Fin 3} {k : ℕ} (h : ∀ i, i < k → u i = v i) :
    dist (rho ⟨codeB u, codeB_mem_attractor u⟩) (rho ⟨codeB v, codeB_mem_attractor v⟩)
      ≤ 2 * (2⁻¹ : ℝ) ^ k := by
  rw [rho_codeB, rho_codeB]
  show dist (Gasket.coding u) (Gasket.coding v) ≤ _
  exact Gasket.dist_coding_le_of_prefix (fun i hi => h i hi)

/-- **`ChainContinuous rho` is exactly `AddressesConverge`.**  Everything
analytic has been discharged; what is left is combinatorics of the order on
`𝒦`. -/
theorem chainContinuous_of_addressesConverge (h : AddressesConverge) :
    ChainContinuous rho := by
  intro x hmono c hc
  -- name the addresses
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
