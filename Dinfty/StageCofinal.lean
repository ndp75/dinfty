import Dinfty.StageEmbedding

open GluingTowerLibrary SierpinskiApplication

-- [D-3388] §The-residue-only-needs-cofinally-many-levels
open scoped Classical

namespace StageRigidity

open EpPairTower

variable {T : EpPairTower}

-- [D-3389] §1-One-stable-level-is-a-fixed-level
-- [D-3390] fixes_stage
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

-- [D-3391] §2-Cofinally-many-stable-levels-suffice
-- [D-3392] StageDefinableCofinal
def StageDefinableCofinal (T : EpPairTower) : Prop :=
  ∀ (θ : T.Bilim ≃o T.Bilim) (N : ℕ), ∃ k, N ≤ k ∧
    ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y

-- [D-3393] stageDefinable_cofinal
theorem stageDefinable_cofinal (h : StageDefinable T) : StageDefinableCofinal T :=
  fun θ N => ⟨N, le_refl N, h θ N⟩

-- [D-3394] fixes_stages_below
theorem fixes_stages_below (hr : LevelsMaximallyRigid T) (θ : T.Bilim ≃o T.Bilim)
    {j k : ℕ} (hjk : j ≤ k)
    (hs : ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y)
    (x : T.carrier j) : θ (T.ins j x) = T.ins j x := by
  rw [← EpPairTower.ins_embLe hjk x]
  exact fixes_stage hr θ k hs _

-- [D-3395] eq_refl_of_cofinal_stable
theorem eq_refl_of_cofinal_stable (hr : LevelsMaximallyRigid T) (θ : T.Bilim ≃o T.Bilim)
    (hcof : ∀ N : ℕ, ∃ k, N ≤ k ∧
      ∀ x : T.carrier k, ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y) :
    θ = OrderIso.refl T.Bilim := by
  refine eq_refl_of_fixes_stages θ (fun j x => ?_)
  obtain ⟨k, hjk, hs⟩ := hcof j
  exact fixes_stages_below hr θ hjk hs x

-- [D-3396] rigid_of_cofinal_stageDefinable
theorem rigid_of_cofinal_stageDefinable (hr : LevelsMaximallyRigid T)
    (hs : StageDefinableCofinal T) : Subsingleton (T.Bilim ≃o T.Bilim) :=
  ⟨fun a b => (eq_refl_of_cofinal_stable hr a (hs a)).trans
    (eq_refl_of_cofinal_stable hr b (hs b)).symm⟩

end StageRigidity

-- [D-3397] §3-Stage-maps-named
namespace StageCofinal

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding

variable {θ : B ≃o B} {k m m' : ℕ}

-- [D-3398] IsStageMap
def IsStageMap (θ : B ≃o B) (k m : ℕ) (f : D (k + 1) → D (m + 1)) : Prop :=
  ∀ x, θ (insD k x) = insD m (f x)

-- [D-3399] stage_map_exists'
theorem stage_map_exists' (θ : B ≃o B) (k : ℕ) :
    ∃ m, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1), IsStageMap θ k m f := by
  obtain ⟨m, hkm, f, hdef, -, -, -, -, -⟩ := StageEmbedding.stage_map_exists θ k
  exact ⟨m, hkm, f, hdef⟩

-- [D-3400] IsStageMap.unique
theorem IsStageMap.unique {f f' : D (k + 1) → D (m + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ k m f') : f = f' := by
  funext x
  exact insD_injective m ((hf x).symm.trans (hf' x))

-- [D-3401] IsStageMap.monotone
theorem IsStageMap.monotone {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f) :
    Monotone f := by
  intro a b hab
  have h1 : insD m (f a) ≤ insD m (f b) := by
    rw [← hf a, ← hf b]; exact θ.monotone (insD_monotone k hab)
  exact (insD_le_insD_iff m _ _).mp h1

-- [D-3402] IsStageMap.reflect
theorem IsStageMap.reflect {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f)
    (a b : D (k + 1)) (h : f a ≤ f b) : a ≤ b := by
  have h1 : θ (insD k a) ≤ θ (insD k b) := by
    rw [hf a, hf b]; exact insD_monotone m h
  exact (insD_le_insD_iff k a b).mp (θ.le_iff_le.mp h1)

-- [D-3403] IsStageMap.injective
theorem IsStageMap.injective {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f) :
    Function.Injective f := fun a b hab =>
  le_antisymm (hf.reflect a b hab.le) (hf.reflect b a hab.ge)

-- [D-3404] IsStageMap.push
theorem IsStageMap.push {f : D (k + 1) → D (m + 1)} (hf : IsStageMap θ k m f)
    (h : m ≤ m') : IsStageMap θ k m' (fun x => embD h (f x)) := by
  intro x
  rw [insD_embD h (f x)]
  exact hf x

-- [D-3405] isStageMap_coherent
theorem isStageMap_coherent {f : D (k + 1) → D (m + 1)} {f' : D (k + 2) → D (m' + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ (k + 1) m' f')
    (hmm : m ≤ m') (hk : k ≤ k + 1) (x : D (k + 1)) :
    embD hmm (f x) = f' (embD hk x) := by
  refine insD_injective m' ?_
  rw [insD_embD hmm (f x), ← hf x, ← hf' (embD hk x), insD_embD hk x]

-- [D-3406] §4-The-diagonal-collapses
-- [D-3407] IsStageMap.diagonal
theorem IsStageMap.diagonal {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f) :
    f = id :=
  TowerRigidity.D_monotone_injection_eq_id (k + 1) hf.monotone hf.injective

-- [D-3408] IsStageMap.fixes
theorem IsStageMap.fixes {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f)
    (x : D (k + 1)) : θ (insD k x) = insD k x := by
  have hx : f x = x := congrFun hf.diagonal x
  rw [hf x, hx]

end StageCofinal

-- [D-3409] §5-At-the-tower
namespace PhiRigidity

open PhiIterateTower PhiBilimit EpPairTower StageRigidity StageEmbedding StageCofinal

-- [D-3410] PhiStageDefinableCofinal
def PhiStageDefinableCofinal : Prop :=
  ∀ (θ : B ≃o B) (N : ℕ), ∃ k, N ≤ k ∧ ∃ f : D (k + 1) → D (k + 1), IsStageMap θ k k f

-- [D-3411] phiStageDefinable_cofinal
theorem phiStageDefinable_cofinal (h : PhiStageDefinable) : PhiStageDefinableCofinal := by
  intro θ N
  exact ⟨N, le_refl N, fun x => Classical.choose (h θ N x),
    fun x => Classical.choose_spec (h θ N x)⟩

-- [D-3412] eq_id_of_cofinal
theorem eq_id_of_cofinal (h : PhiStageDefinableCofinal) (θ : B ≃o B) :
    θ = OrderIso.refl B := by
  refine StageRigidity.eq_refl_of_cofinal_stable levels_maximally_rigid θ (fun N => ?_)
  obtain ⟨k, hNk, f, hf⟩ := h θ N
  exact ⟨k, hNk, fun x => ⟨x, hf.fixes x⟩⟩

-- [D-3413] B_rigid_of_cofinal
theorem B_rigid_of_cofinal (h : PhiStageDefinableCofinal) : Subsingleton (B ≃o B) :=
  ⟨fun a b => (eq_id_of_cofinal h a).trans (eq_id_of_cofinal h b).symm⟩

end PhiRigidity
