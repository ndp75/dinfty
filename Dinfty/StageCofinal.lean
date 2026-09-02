import Dinfty.StageEmbedding

open GluingTowerLibrary SierpinskiApplication

/-!
# The residue only needs *cofinally many* levels

§117 killed the sufficient condition (`LevelEmbUnique`) and named the fallback:
work from the **necessary** condition, `StageEmbedding.stage_map_comp`.  This
module does that, and the result is a strict weakening of the residue itself.

## What the necessary condition actually says

`stage_map_exists` says an automorphism `θ` of `B` carries stage `k` into some
later stage `m` by a bounded join-embedding `f`.  Package that as
`IsStageMap θ k m f`.  Three facts are then free:

* **uniqueness** — `insD m` is injective, so `f` is determined by `θ, k, m`;
* **pushing** — a stage map into `m` is one into any `m' ≥ m`, via `embD`;
* **coherence** — the stage maps of a single `θ` commute with the tower's own
  embeddings (`isStageMap_coherent`).  This is the content of `stage_map_comp`
  in the form that is actually usable: the family is not a loose collection of
  embeddings, it is a morphism of the whole stage filtration.

## The payoff: the diagonal collapses

If a stage map lands back on its own level — `IsStageMap θ k k f` — then `f` is
a monotone injection of `D (k+1)`, hence the identity
(`TowerRigidity.D_monotone_injection_eq_id`), so `θ` fixes stage `k`
**pointwise**.  Combined with `ins_embLe`, fixing stage `k` fixes every earlier
stage too.  So the levels at which `θ` is stage-preserving are automatically
levels at which `θ` is the identity, and they are downward closed.

Hence `eq_refl_of_cofinal_stable`: an automorphism of *any* ep-pair tower's
bilimit with maximally rigid levels is the identity as soon as it is
stage-preserving at **cofinally many** levels — not at all of them.

```lean
StageRigidity.rigid_of_cofinal_stageDefinable :
  LevelsMaximallyRigid T → StageDefinableCofinal T → Subsingleton (T.Bilim ≃o T.Bilim)
PhiRigidity.B_rigid_of_cofinal : PhiStageDefinableCofinal → Subsingleton (B ≃o B)
```

This does not close the residue.  It replaces "for every `θ` and **every** `k`,
`θ` preserves stage `k`" by "for every `θ` and **arbitrarily large** `k`", which
is what one gets to assume when hunting a single witness level.
-/

open scoped Classical

namespace StageRigidity

open EpPairTower

variable {T : EpPairTower}

/-! ## 1.  One stable level is a *fixed* level -/

/-- If `θ` carries stage `k` into stage `k`, it fixes stage `k` pointwise.  The
level's own rigidity does all the work: the induced map is a monotone injection
of `T.carrier k`. -/
theorem fixes_stage (hr : LevelsMaximallyRigid T) (θ : T.Bilim ≃o T.Bilim) (k : ℕ)
    (hs : ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y)
    (x : T.carrier k) : θ (T.ins k x) = T.ins k x := by
  choose f hf using hs
  have hmono : Monotone f := by
    intro a b hab
    have h2 : θ (T.ins k a) ≤ θ (T.ins k b) := θ.monotone ((ins_le_iff k a b).mpr hab)
    rw [hf a, hf b] at h2
    exact (ins_le_iff k (f a) (f b)).mp h2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : θ (T.ins k a) = θ (T.ins k b) := by rw [hf a, hf b, hab]
    exact ins_injective k (θ.injective h1)
  have hid : f x = x := congrFun (hr k f hmono hinj) x
  rw [hf x, hid]

/-! ## 2.  Cofinally many stable levels suffice -/

/-- The residue, weakened: each automorphism need only be stage-preserving at
arbitrarily large levels, not at every level. -/
def StageDefinableCofinal (T : EpPairTower) : Prop :=
  ∀ (θ : T.Bilim ≃o T.Bilim) (N : ℕ), ∃ k, N ≤ k ∧
    ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y

theorem stageDefinable_cofinal (h : StageDefinable T) : StageDefinableCofinal T :=
  fun θ N => ⟨N, le_refl N, h θ N⟩

/-- **Stability is downward closed, and it is identity all the way down.**  One
stable level pins every earlier stage as well, because `ins j` factors through
`ins k` along `embLe`.  This is why cofinality is the right hypothesis: there is
no benefit to assuming stability at small levels, only at large ones. -/
theorem fixes_stages_below (hr : LevelsMaximallyRigid T) (θ : T.Bilim ≃o T.Bilim)
    {j k : ℕ} (hjk : j ≤ k)
    (hs : ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y)
    (x : T.carrier j) : θ (T.ins j x) = T.ins j x := by
  rw [← EpPairTower.ins_embLe hjk x]
  exact fixes_stage hr θ k hs _

/-- **The strengthening.**  A stable level fixes every earlier stage as well
(`ins_embLe`), so cofinally many stable levels fix all of them. -/
theorem eq_refl_of_cofinal_stable (hr : LevelsMaximallyRigid T) (θ : T.Bilim ≃o T.Bilim)
    (hcof : ∀ N : ℕ, ∃ k, N ≤ k ∧
      ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y) :
    θ = OrderIso.refl T.Bilim := by
  refine eq_refl_of_fixes_stages θ (fun j x => ?_)
  obtain ⟨k, hjk, hs⟩ := hcof j
  exact fixes_stages_below hr θ hjk hs x

theorem rigid_of_cofinal_stageDefinable (hr : LevelsMaximallyRigid T)
    (hs : StageDefinableCofinal T) : Subsingleton (T.Bilim ≃o T.Bilim) :=
  ⟨fun a b => (eq_refl_of_cofinal_stable hr a (hs a)).trans
    (eq_refl_of_cofinal_stable hr b (hs b)).symm⟩

end StageRigidity

/-! ## 3.  Stage maps, named -/

namespace StageCofinal

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding

variable {θ : B ≃o B} {k m m' : ℕ}

/-- `f` is *the* stage map of `θ` from level `k` into level `m`. -/
def IsStageMap (θ : B ≃o B) (k m : ℕ) (f : D (k + 1) → D (m + 1)) : Prop :=
  ∀ x, θ (insD k x) = insD m (f x)

theorem stage_map_exists' (θ : B ≃o B) (k : ℕ) :
    ∃ m, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1), IsStageMap θ k m f := by
  obtain ⟨m, hkm, f, hdef, -, -, -, -, -⟩ := StageEmbedding.stage_map_exists θ k
  exact ⟨m, hkm, f, hdef⟩

/-- Determined by `θ`, `k`, `m`. -/
theorem IsStageMap.unique {f f' : D (k + 1) → D (m + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ k m f') : f = f' := by
  funext x
  exact insD_injective m ((hf x).symm.trans (hf' x))

theorem IsStageMap.monotone {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f) :
    Monotone f := by
  intro a b hab
  have h1 : insD m (f a) ≤ insD m (f b) := by
    rw [← hf a, ← hf b]; exact θ.monotone (insD_monotone k hab)
  exact (insD_le_insD_iff m _ _).mp h1

theorem IsStageMap.reflect {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f)
    (a b : D (k + 1)) (h : f a ≤ f b) : a ≤ b := by
  have h1 : θ (insD k a) ≤ θ (insD k b) := by
    rw [hf a, hf b]; exact insD_monotone m h
  exact (insD_le_insD_iff k a b).mp (θ.le_iff_le.mp h1)

theorem IsStageMap.injective {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f) :
    Function.Injective f := fun a b hab =>
  le_antisymm (hf.reflect a b hab.le) (hf.reflect b a hab.ge)

/-- A stage map into `m` is a stage map into any later level. -/
theorem IsStageMap.push {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f)
    (h : m ≤ m') : IsStageMap θ k m' (fun x => embD h (f x)) := by
  intro x
  rw [insD_embD h (f x)]
  exact hf x

/-- **The coherence square** — the usable form of `stage_map_comp`.  The stage
maps of one automorphism commute with the tower's own embeddings, so the family
is a morphism of the entire stage filtration rather than a loose collection. -/
theorem isStageMap_coherent {f : D (k + 1) → D (m + 1)} {f' : D (k + 2) → D (m' + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ (k + 1) m' f')
    (hmm : m ≤ m') (hk : k ≤ k + 1) (x : D (k + 1)) :
    embD hmm (f x) = f' (embD hk x) := by
  refine insD_injective m' ?_
  rw [insD_embD hmm (f x), ← hf x, ← hf' (embD hk x), insD_embD hk x]

/-! ## 4.  The diagonal collapses -/

/-- A stage map that lands back on its own level **is the identity**. -/
theorem IsStageMap.diagonal {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f) :
    f = id :=
  TowerRigidity.D_monotone_injection_eq_id (k + 1) hf.monotone hf.injective

/-- …so `θ` fixes that stage pointwise. -/
theorem IsStageMap.fixes {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f)
    (x : D (k + 1)) : θ (insD k x) = insD k x := by
  have hx : f x = x := congrFun hf.diagonal x
  rw [hf x, hx]

end StageCofinal

/-! ## 5.  At the `Φ`-tower -/

namespace PhiRigidity

open PhiIterateTower PhiBilimit EpPairTower StageRigidity StageEmbedding StageCofinal

/-- **The residue, weakened.**  Only cofinally many stable levels per
automorphism, instead of every level. -/
def PhiStageDefinableCofinal : Prop :=
  ∀ (θ : B ≃o B) (N : ℕ), ∃ k, N ≤ k ∧ ∃ f : D (k + 1) → D (k + 1), IsStageMap θ k k f

theorem phiStageDefinable_cofinal (h : PhiStageDefinable) : PhiStageDefinableCofinal := by
  intro θ N
  exact ⟨N, le_refl N, fun x => Classical.choose (h θ N x),
    fun x => Classical.choose_spec (h θ N x)⟩

theorem eq_id_of_cofinal (h : PhiStageDefinableCofinal) (θ : B ≃o B) :
    θ = OrderIso.refl B := by
  refine StageRigidity.eq_refl_of_cofinal_stable levels_maximally_rigid θ (fun N => ?_)
  obtain ⟨k, hNk, f, hf⟩ := h θ N
  exact ⟨k, hNk, fun x => ⟨x, hf.fixes x⟩⟩

/-- **Theorem A's carrier is rigid from cofinally many stable levels.** -/
theorem B_rigid_of_cofinal (h : PhiStageDefinableCofinal) : Subsingleton (B ≃o B) :=
  ⟨fun a b => (eq_id_of_cofinal h a).trans (eq_id_of_cofinal h b).symm⟩

end PhiRigidity
