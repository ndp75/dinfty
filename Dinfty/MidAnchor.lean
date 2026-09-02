import Dinfty.DInftyNoFootholds

open GluingTowerLibrary SierpinskiApplication

-- [D-1658] §Where-they-cancel-the-seam-and-a-canonical
open scoped Classical

namespace MidAnchor

open Assembly ColimitCompatPipe JoinIrredDInfty

-- [D-1659] §The-marked-points-are-colimit-coherent
-- [D-1660] dMid_succ_eq_iotaD
theorem dMid_succ_eq_iotaD (k : ℕ) : dMid (k + 1) = iotaD k (dMid k) := rfl

-- [D-1661] iotaLe_dMid
theorem iotaLe_dMid {k n : ℕ} (h : k ≤ n) : iotaLe h (dMid k) = dMid n := by
  induction n, h using Nat.le_induction with
  | base => exact iotaLe_self _ _
  | succ m hm ih =>
      rw [iotaLe_succ hm (Nat.le_succ_of_le hm), ih, ← dMid_succ_eq_iotaD]

-- [D-1662] midInf
noncomputable def midInf : DInfty := toD 0 (dMid 0)

-- [D-1663] toD_dMid
theorem toD_dMid (k : ℕ) : toD k (dMid k) = midInf := by
  rw [midInf, ← toD_iotaLe (Nat.zero_le k) (dMid 0), iotaLe_dMid]

-- [D-1664] §midInf-is-interior-on-both-sides
-- [D-1665] midInf_ne_bot
theorem midInf_ne_bot : midInf ≠ (⊥ : DInfty) := fun h =>
  dMid_ne_bot 0 ((toD_eq_bot_iff 0 (dMid 0)).mp h)

-- [D-1666] bot_lt_midInf
theorem bot_lt_midInf : (⊥ : DInfty) < midInf :=
  lt_of_le_of_ne bot_le (Ne.symm midInf_ne_bot)

-- [D-1667] midInf_lt_toD_top
theorem midInf_lt_toD_top (k : ℕ) : midInf < toD k (⊤ : D k) := by
  rw [← toD_dMid k]
  refine lt_of_le_of_ne ((toD_le_iff' k _ _).mpr le_top) ?_
  intro h
  exact dMid_ne_top k (toD_inj k h)

-- [D-1668] §An-automorphism-that-maps-a-stage-into-itself
-- [D-1669] fixes_stage_of_maps_into
theorem fixes_stage_of_maps_into (θ : DInfty ≃o DInfty) (k : ℕ)
    (h : ∀ x : D k, ∃ y : D k, θ (toD k x) = toD k y) (x : D k) :
    θ (toD k x) = toD k x := by
  choose f hf using h
  have hmono : Monotone f := by
    intro a b hab
    have h2 : θ (toD k a) ≤ θ (toD k b) := θ.monotone ((toD_le_iff' k a b).mpr hab)
    rw [hf a, hf b] at h2
    exact (toD_le_iff' k (f a) (f b)).mp h2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : θ (toD k a) = θ (toD k b) := by rw [hf a, hf b, hab]
    exact toD_inj k (θ.injective h1)
  have hid : f = id := TowerRigidity.D_monotone_injection_eq_id k hmono hinj
  rw [hf x, congrFun hid x]
  rfl

-- [D-1670] fixes_midInf_of_maps_into
theorem fixes_midInf_of_maps_into (θ : DInfty ≃o DInfty)
    (h : ∀ x : D 0, ∃ y : D 0, θ (toD 0 x) = toD 0 y) : θ midInf = midInf := by
  rw [midInf]
  exact fixes_stage_of_maps_into θ 0 h (dMid 0)

-- [D-1671] fixes_toD_zero_top_of_maps_into
theorem fixes_toD_zero_top_of_maps_into (θ : DInfty ≃o DInfty)
    (h : ∀ x : D 0, ∃ y : D 0, θ (toD 0 x) = toD 0 y) :
    θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0) :=
  fixes_stage_of_maps_into θ 0 h (⊤ : D 0)

-- [D-1672] stage_zero_eq
theorem stage_zero_eq :
    Set.range (toD 0) = {(⊥ : DInfty), midInf, toD 0 (⊤ : D 0)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
      show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
      revert x; decide
    rcases this with h | h | h
    · left; rw [h, ← bot_eq_toD 0]
    · right; left; rw [h, midInf]
    · right; right; rw [h]; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨(⊥ : D 0), (bot_eq_toD 0).symm⟩
    · exact ⟨dMid 0, rfl⟩
    · exact ⟨(⊤ : D 0), rfl⟩

end MidAnchor
