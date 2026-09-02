import Dinfty.CopyIdeal

open GluingTowerLibrary SierpinskiApplication

-- [D-3273] §Does-Theorem-B-s-rigidity-survive-from-the-copy
open scoped Classical

open Set

universe u

namespace StageRigidity

open EpPairTower

variable {T : EpPairTower}

-- [D-3274] §1-The-stage-maps-are-order-embeddings
-- [D-3275] ins_le_iff
theorem ins_le_iff (k : ℕ) (w w' : T.carrier k) : T.ins k w ≤ T.ins k w' ↔ w ≤ w' := by
  constructor
  · intro h
    have hk := h k
    rwa [ins_self k w, ins_self k w'] at hk
  · exact fun h => ins_monotone k h

-- [D-3276] ins_le_iff'
theorem ins_le_iff' (k : ℕ) (a : T.carrier k) (u : T.Bilim) :
    T.ins k a ≤ u ↔ a ≤ u.1 k := by
  constructor
  · intro h
    have hk := h k
    rwa [ins_self k a] at hk
  · intro h
    exact (ins_monotone k h).trans (ins_le_self u k)

-- [D-3277] ins_injective
theorem ins_injective (k : ℕ) : Function.Injective (T.ins k) := fun w w' h =>
  le_antisymm ((ins_le_iff k w w').mp h.le) ((ins_le_iff k w' w).mp h.ge)

-- [D-3278] §2-The-two-hypotheses
-- [D-3279] StageDefinable
def StageDefinable (T : EpPairTower) : Prop :=
  ∀ (θ : T.Bilim ≃o T.Bilim) (k : ℕ) (x : T.carrier k),
    ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y

-- [D-3280] LevelsMaximallyRigid
def LevelsMaximallyRigid (T : EpPairTower) : Prop :=
  ∀ (k : ℕ) (f : T.carrier k → T.carrier k), Monotone f → Function.Injective f → f = id

-- [D-3281] §3-The-transport
-- [D-3282] eq_on_stages
theorem eq_on_stages (hr : LevelsMaximallyRigid T) (hs : StageDefinable T)
    (θ : T.Bilim ≃o T.Bilim) (k : ℕ) (x : T.carrier k) : θ (T.ins k x) = T.ins k x := by
  choose f hf using hs θ k
  have hmono : Monotone f := by
    intro a b hab
    have h2 : θ (T.ins k a) ≤ θ (T.ins k b) := θ.monotone ((ins_le_iff k a b).mpr hab)
    rw [hf a, hf b] at h2
    exact (ins_le_iff k (f a) (f b)).mp h2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : θ (T.ins k a) = θ (T.ins k b) := by rw [hf a, hf b, hab]
    exact ins_injective k (θ.injective h1)
  have hid : f = id := hr k f hmono hinj
  rw [hf x, congrFun hid x]
  rfl

-- [D-3283] eq_refl_of_fixes_stages
theorem eq_refl_of_fixes_stages (θ : T.Bilim ≃o T.Bilim)
    (key : ∀ (k : ℕ) (x : T.carrier k), θ (T.ins k x) = T.ins k x) :
    θ = OrderIso.refl T.Bilim := by
  refine RelIso.ext (fun z => ?_)
  have h1 : IsLUB (T.chainSet z) z := chainSet_isLUB z
  have h2 : IsLUB (θ '' T.chainSet z) (θ z) := (OrderIso.isLUB_image' θ).mpr h1
  have h3 : θ '' T.chainSet z = T.chainSet z := by
    ext u
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (key n (z.1 n)).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨T.ins n (z.1 n), ⟨n, rfl⟩, key n (z.1 n)⟩
  rw [h3] at h2
  exact h2.unique h1

-- [D-3284] eq_refl_of_stageDefinable
theorem eq_refl_of_stageDefinable (hr : LevelsMaximallyRigid T) (hs : StageDefinable T)
    (θ : T.Bilim ≃o T.Bilim) : θ = OrderIso.refl T.Bilim :=
  eq_refl_of_fixes_stages θ (eq_on_stages hr hs θ)

-- [D-3285] rigid_of_stageDefinable
theorem rigid_of_stageDefinable (hr : LevelsMaximallyRigid T) (hs : StageDefinable T) :
    Subsingleton (T.Bilim ≃o T.Bilim) :=
  ⟨fun a b => (eq_refl_of_stageDefinable hr hs a).trans
    (eq_refl_of_stageDefinable hr hs b).symm⟩

end StageRigidity

-- [D-3286] §4-At-the-tower
namespace PhiRigidity

open PhiIterateTower PhiBilimit EpPairTower StageRigidity

-- [D-3287] PhiStageDefinable
def PhiStageDefinable : Prop := StageDefinable phiTowerEP

-- [D-3288] levels_maximally_rigid
theorem levels_maximally_rigid : LevelsMaximallyRigid phiTowerEP :=
  fun k f hmono hinj => TowerRigidity.D_monotone_injection_eq_id (k + 1) hmono hinj

-- [D-3289] B_rigid_of_stageDefinable
theorem B_rigid_of_stageDefinable (h : PhiStageDefinable) : Subsingleton (B ≃o B) :=
  rigid_of_stageDefinable levels_maximally_rigid h

-- [D-3290] eq_id_of_stageDefinable
theorem eq_id_of_stageDefinable (h : PhiStageDefinable) (θ : B ≃o B) :
    θ = OrderIso.refl B :=
  eq_refl_of_stageDefinable levels_maximally_rigid h θ

-- [D-3291] §Why-restriction-to-the-copy-A-ideal-cannot-be
-- [D-3292] legacy_subtower
theorem legacy_subtower (k : ℕ) (x : D k) :
    glueAA k (iotaD k x) = iotaD (k + 1) (iotaD k x) := glueAA_iotaD k x

-- [D-3293] phi_emb_top_not_legacy
theorem phi_emb_top_not_legacy (n : ℕ) (x : D (n + 1)) :
    (iter n).emb (⊤ : D (n + 1)) ≠ iotaD (n + 1) x := by
  rw [(iter n).emb_top]
  exact fun hc => iotaD_ne_top (n + 1) x hc.symm

-- [D-3294] ins_top
theorem ins_top (n : ℕ) : phiTowerEP.ins n (⊤ : D (n + 1)) = topB :=
  PhiBilimit.ins_top n

-- [D-3295] §The-two-pillars-now-rest-on-one-reduction
-- [D-3296] pillars_share_one_reduction
theorem pillars_share_one_reduction :
    (PhiStageDefinable → Subsingleton (B ≃o B))
      ∧ Subsingleton (DBilimit ≃o DBilimit) :=
  ⟨B_rigid_of_stageDefinable, CopyCHigh.DBilimit_rigid⟩

end PhiRigidity
