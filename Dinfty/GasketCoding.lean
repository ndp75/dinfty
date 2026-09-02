import Dinfty.Gasket

/-!
# The coding map `π : {A,B,C}^ℕ ↠ Γ`

`CoreIFS`'s `rho` is, in the companion note, `ρ = π ∘ α⁻¹`: the address map `π`
composed with a coding `α` of `D∞`'s attractor by addresses.  This module builds
the first factor, `π`, and proves the three properties `TheoremAData` asks of
`rho` that are about `π` alone:

* `coding_mem` / `codeGamma` — `π` lands in `Γ`;
* `continuous_codeGamma` — `π` is continuous;
* `codeGamma_surjective` — `π` is onto;
* `coding_cons` — `π` is equivariant: `π (j :: w) = f_j (π w)`.

Nothing here is about `D∞`.  This is the classical half, and it is the half that
can be checked without any of the tower machinery.

The construction is the usual one: `π w` is the limit of
`h_{w 0} ∘ ⋯ ∘ h_{w (n-1)}` applied to a basepoint.  Contraction makes the
sequence Cauchy at rate `2⁻ⁿ`, which is also what gives continuity (agreeing
prefixes ⇒ close images) and surjectivity (any gasket point has an address,
obtained by peeling the self-similarity identity).
-/

open Metric Set Filter Topology

namespace Gasket

/-! ## 1.  The three maps, indexed -/

noncomputable def cw (j : Fin 3) : E := if j = 0 then cA else if j = 1 then cB else cC

noncomputable def step (j : Fin 3) : E → E := contract (cw j)

theorem step_lipschitz (j : Fin 3) : LipschitzWith (2⁻¹ : NNReal) (step j) :=
  contract_lipschitz _

theorem step_continuous (j : Fin 3) : Continuous (step j) := (step_lipschitz j).continuous

theorem step_mapsTo (j : Fin 3) : MapsTo (step j) gasketSet gasketSet := by
  fin_cases j
  · simpa [step, cw] using mapsTo_cA
  · simpa [step, cw] using mapsTo_cB
  · simpa [step, cw] using mapsTo_cC

/-- `vA` is the origin, so `h_j vA = c_j`, and every `c_j` is within `2⁻¹` of
it.  The sharp constant matters: it is what makes the gasket fit inside the unit
ball, which is what separates the three sub-gaskets in `GasketNotOpen`. -/
theorem dist_step_vA_le (j : Fin 3) : dist vA (step j vA) ≤ 2⁻¹ := by
  have hv : step j vA = cw j := by
    simp [step, contract, vA, Prod.ext_iff]
  rw [hv]
  fin_cases j <;>
    simp [cw, vA, cA, cB, cC, Prod.dist_eq, Real.dist_eq] <;> norm_num

/-! ## 2.  Prefix maps -/

/-- `pre w n = h_{w 0} ∘ ⋯ ∘ h_{w (n-1)}`. -/
noncomputable def pre (w : ℕ → Fin 3) : ℕ → (E → E)
  | 0 => id
  | (n + 1) => pre w n ∘ step (w n)

@[simp] theorem pre_zero (w : ℕ → Fin 3) : pre w 0 = id := rfl

theorem pre_succ (w : ℕ → Fin 3) (n : ℕ) : pre w (n + 1) = pre w n ∘ step (w n) := rfl

theorem pre_lipschitz (w : ℕ → Fin 3) (n : ℕ) :
    LipschitzWith ((2⁻¹ : NNReal) ^ n) (pre w n) := by
  induction n with
  | zero => simpa using LipschitzWith.id
  | succ n ih =>
      rw [pre_succ, pow_succ]
      exact ih.comp (step_lipschitz (w n))

theorem pre_mapsTo (w : ℕ → Fin 3) (n : ℕ) : MapsTo (pre w n) gasketSet gasketSet := by
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih =>
      rw [pre_succ]
      exact ih.comp (step_mapsTo (w n))

/-- Prefix maps depend only on the prefix. -/
theorem pre_congr {w w' : ℕ → Fin 3} {n : ℕ} (h : ∀ k < n, w k = w' k) :
    pre w n = pre w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pre_succ, pre_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        h n (Nat.lt_succ_self n)]

/-! ## 3.  The approximating sequence and its limit -/

noncomputable def xseq (w : ℕ → Fin 3) (n : ℕ) : E := pre w n vA

theorem xseq_mem (w : ℕ → Fin 3) (n : ℕ) : xseq w n ∈ gasketSet :=
  pre_mapsTo w n vA_mem

theorem dist_xseq_succ (w : ℕ → Fin 3) (n : ℕ) :
    dist (xseq w n) (xseq w (n + 1)) ≤ (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n := by
  have h1 : xseq w (n + 1) = pre w n (step (w n) vA) := by
    simp [xseq, pre_succ]
  rw [h1, xseq]
  have h2 := (pre_lipschitz w n).dist_le_mul vA (step (w n) vA)
  refine h2.trans ?_
  have h3 : ((((2⁻¹ : NNReal)) ^ n : NNReal) : ℝ) = (2⁻¹ : ℝ) ^ n := by
    push_cast
    norm_num
  rw [h3]
  have h4 : (0:ℝ) ≤ (2⁻¹ : ℝ) ^ n := by positivity
  calc (2⁻¹ : ℝ) ^ n * dist vA (step (w n) vA)
      ≤ (2⁻¹ : ℝ) ^ n * 2⁻¹ :=
        mul_le_mul_of_nonneg_left (dist_step_vA_le (w n)) h4
    _ = (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n := by ring

theorem xseq_cauchy (w : ℕ → Fin 3) : CauchySeq (xseq w) :=
  cauchySeq_of_le_geometric (2⁻¹ : ℝ) (2⁻¹ : ℝ) (by norm_num) (dist_xseq_succ w)

/-- **The address map.** -/
noncomputable def coding (w : ℕ → Fin 3) : E := limUnder atTop (xseq w)

theorem coding_tendsto (w : ℕ → Fin 3) : Tendsto (xseq w) atTop (𝓝 (coding w)) :=
  (xseq_cauchy w).tendsto_limUnder

theorem coding_mem (w : ℕ → Fin 3) : coding w ∈ gasketSet :=
  isCompact_gasketSet.isClosed.mem_of_tendsto (coding_tendsto w)
    (Eventually.of_forall (xseq_mem w))

/-- The rate: `π w` is within `2⁻ⁿ` of the `n`-th approximation. -/
theorem dist_xseq_coding (w : ℕ → Fin 3) (n : ℕ) :
    dist (xseq w n) (coding w) ≤ (2⁻¹ : ℝ) ^ n := by
  have h := dist_le_of_le_geometric_of_tendsto (2⁻¹ : ℝ) (2⁻¹ : ℝ) (by norm_num)
    (dist_xseq_succ w) (coding_tendsto w) n
  have e : (2⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ n / (1 - 2⁻¹) = (2⁻¹ : ℝ) ^ n := by
    rw [show (1:ℝ) - 2⁻¹ = 2⁻¹ by norm_num]
    field_simp
  rwa [e] at h

/-- **The gasket sits in the unit ball.**  Immediate from the sharp rate, since
`xseq w 0 = vA`. -/
theorem dist_vA_coding (w : ℕ → Fin 3) : dist vA (coding w) ≤ 1 := by
  have h := dist_xseq_coding w 0
  simpa [xseq] using h

/-! ## 4.  Equivariance -/

/-- `cons j w` — prepend a symbol. -/
def cons (j : Fin 3) (w : ℕ → Fin 3) : ℕ → Fin 3
  | 0 => j
  | (n + 1) => w n

theorem pre_cons (j : Fin 3) (w : ℕ → Fin 3) (n : ℕ) :
    pre (cons j w) (n + 1) = step j ∘ pre w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pre_succ, ih]
      rfl

theorem xseq_cons (j : Fin 3) (w : ℕ → Fin 3) (n : ℕ) :
    xseq (cons j w) (n + 1) = step j (xseq w n) := by
  simp [xseq, pre_cons]

/-- **`π` intertwines the shift with the IFS map.** -/
theorem coding_cons (j : Fin 3) (w : ℕ → Fin 3) :
    coding (cons j w) = step j (coding w) := by
  have h1 : Tendsto (fun n => xseq (cons j w) (n + 1)) atTop (𝓝 (coding (cons j w))) :=
    (coding_tendsto (cons j w)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => xseq (cons j w) (n + 1)) atTop (𝓝 (step j (coding w))) := by
    have := ((step_continuous j).tendsto (coding w)).comp (coding_tendsto w)
    simpa [Function.comp_def, xseq_cons] using this
  exact tendsto_nhds_unique h1 h2

/-! ## 5.  Surjectivity -/

theorem exists_pred {g : E} (hg : g ∈ gasketSet) :
    ∃ j : Fin 3, ∃ g' ∈ gasketSet, step j g' = g := by
  rw [gasketSet_eq] at hg
  rcases hg with (⟨x, hx, hxg⟩ | ⟨x, hx, hxg⟩) | ⟨x, hx, hxg⟩
  · exact ⟨0, x, hx, by simpa [step, cw] using hxg⟩
  · exact ⟨1, x, hx, by simpa [step, cw] using hxg⟩
  · exact ⟨2, x, hx, by simpa [step, cw] using hxg⟩

/-- One peeling step, as a function on the gasket. -/
noncomputable def peel (p : gasketSet) : Fin 3 × gasketSet :=
  let h := exists_pred p.2
  ⟨h.choose, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩⟩

theorem peel_spec (p : gasketSet) : step (peel p).1 ((peel p).2 : E) = (p : E) :=
  (exists_pred p.2).choose_spec.choose_spec.2

noncomputable def orbit (p : gasketSet) : ℕ → gasketSet
  | 0 => p
  | (n + 1) => (peel (orbit p n)).2

noncomputable def addr (p : gasketSet) : ℕ → Fin 3 := fun n => (peel (orbit p n)).1

theorem orbit_step (p : gasketSet) (n : ℕ) :
    step (addr p n) ((orbit p (n + 1) : gasketSet) : E) = ((orbit p n : gasketSet) : E) :=
  peel_spec (orbit p n)

theorem pre_orbit (p : gasketSet) (n : ℕ) :
    pre (addr p) n ((orbit p n : gasketSet) : E) = (p : E) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pre_succ]
      show pre (addr p) n (step (addr p n) ((orbit p (n + 1) : gasketSet) : E)) = (p : E)
      rw [orbit_step p n, ih]

/-- The `n`-th approximation to the address of `p` is `2⁻ⁿ`-close to `p`. -/
theorem dist_xseq_addr {M : ℝ} (hM : gasketSet ⊆ closedBall vA M) (p : gasketSet) (n : ℕ) :
    dist (xseq (addr p) n) (p : E) ≤ (2⁻¹ : ℝ) ^ n * M := by
  have h1 : ((p : E)) = pre (addr p) n ((orbit p n : gasketSet) : E) := (pre_orbit p n).symm
  rw [xseq, h1]
  have h2 := (pre_lipschitz (addr p) n).dist_le_mul vA ((orbit p n : gasketSet) : E)
  have h3 : ((((2⁻¹ : NNReal)) ^ n : NNReal) : ℝ) = (2⁻¹ : ℝ) ^ n := by
    push_cast; norm_num
  rw [h3] at h2
  refine h2.trans ?_
  have h4 : (0:ℝ) ≤ (2⁻¹ : ℝ) ^ n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h4
  exact mem_closedBall'.1 (hM (orbit p n).2)

/-- **`π` is onto the gasket.** -/
theorem coding_surjOn : ∀ g ∈ gasketSet, ∃ w : ℕ → Fin 3, coding w = g := by
  intro g hg
  obtain ⟨M, hM⟩ := isCompact_gasketSet.isBounded.subset_closedBall vA
  refine ⟨addr ⟨g, hg⟩, ?_⟩
  have htend : Tendsto (fun n => xseq (addr ⟨g, hg⟩) n) atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (dist_xseq_addr hM ⟨g, hg⟩) ?_
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    simpa using h.mul_const M
  exact tendsto_nhds_unique (coding_tendsto _) htend

/-- **`Γ ⊆ closedBall vA 1`.** -/
theorem gasketSet_subset_closedBall : gasketSet ⊆ closedBall vA 1 := by
  intro g hg
  obtain ⟨w, hw⟩ := coding_surjOn g hg
  rw [← hw]
  have h := dist_vA_coding w
  rw [dist_comm] at h
  exact mem_closedBall.2 h

/-! ## 6.  Continuity -/

theorem coding_eq_of_prefix {w w' : ℕ → Fin 3} {n : ℕ} (h : ∀ k < n, w k = w' k) :
    xseq w n = xseq w' n := by
  rw [xseq, xseq, pre_congr h]

/-- **The prefix estimate.**  Agreeing on the first `k` symbols pins the image to
within `2 · 2⁻ᵏ`.  This is the whole content of continuity, and it is what any
notion of continuity on the domain side has to reproduce. -/
theorem dist_coding_le_of_prefix {u v : ℕ → Fin 3} {k : ℕ} (h : ∀ i < k, u i = v i) :
    dist (coding u) (coding v) ≤ 2 * (2⁻¹ : ℝ) ^ k := by
  have hpre : xseq u k = xseq v k := coding_eq_of_prefix h
  calc dist (coding u) (coding v)
      ≤ dist (coding u) (xseq u k) + dist (xseq u k) (coding v) := dist_triangle _ _ _
    _ = dist (xseq u k) (coding u) + dist (xseq v k) (coding v) := by
        rw [dist_comm (coding u) (xseq u k), hpre]
    _ ≤ (2⁻¹ : ℝ) ^ k + (2⁻¹ : ℝ) ^ k :=
        add_le_add (dist_xseq_coding u k) (dist_xseq_coding v k)
    _ = 2 * (2⁻¹ : ℝ) ^ k := by ring

theorem continuous_coding : Continuous coding := by
  rw [continuous_iff_continuousAt]
  intro w
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * (2⁻¹ : ℝ) ^ n < ε := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹:ℝ) < 1)
    have h2 : Tendsto (fun n : ℕ => 2 * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using h.const_mul 2
    exact ((h2.eventually (gt_mem_nhds hε)).exists)
  have hcyl : ∀ᶠ w' in 𝓝 w, ∀ k ∈ Finset.range n, w' k = w k := by
    refine (Filter.eventually_all_finset _).2 fun k _ => ?_
    exact (continuous_apply k).continuousAt.preimage_mem_nhds
      ((isOpen_discrete ({w k} : Set (Fin 3))).mem_nhds rfl)
  filter_upwards [hcyl] with w' hw'
  exact lt_of_le_of_lt
    (dist_coding_le_of_prefix (fun k hk => hw' k (Finset.mem_range.2 hk))) hn

/-! ## 7.  …valued in `Γ` -/

/-- **`π`, as a map into `Γ`.** -/
noncomputable def codeGamma (w : ℕ → Fin 3) : Gamma := ⟨coding w, coding_mem w⟩

theorem continuous_codeGamma : Continuous codeGamma :=
  Continuous.subtype_mk continuous_coding _

theorem codeGamma_surjective : Function.Surjective codeGamma := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw⟩ := coding_surjOn g hg
  exact ⟨w, Subtype.ext hw⟩

theorem codeGamma_cons_zero (w : ℕ → Fin 3) :
    codeGamma (cons 0 w) = fA (codeGamma w) := by
  refine Subtype.ext ?_
  simpa [step, cw, fA, codeGamma] using coding_cons 0 w

theorem codeGamma_cons_one (w : ℕ → Fin 3) :
    codeGamma (cons 1 w) = fB (codeGamma w) := by
  refine Subtype.ext ?_
  simpa [step, cw, fB, codeGamma] using coding_cons 1 w

theorem codeGamma_cons_two (w : ℕ → Fin 3) :
    codeGamma (cons 2 w) = fC (codeGamma w) := by
  refine Subtype.ext ?_
  simpa [step, cw, fC, codeGamma] using coding_cons 2 w

end Gasket
