import Dinfty.JoinIrredLevelStable

open GluingTowerLibrary SierpinskiApplication

-- [D-1602] §Assembly-scaffold-the-pillars-reductions
open scoped Classical

namespace Assembly

-- [D-1603] StageDefinable
def StageDefinable : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), ∃ y : D k, θ (toD k x) = toD k y

-- [D-1604] toD_inj
theorem toD_inj (k : ℕ) : Function.Injective (toD k) := fun x y h =>
  le_antisymm ((toD_le_iff' k x y).mp (le_of_eq h))
    ((toD_le_iff' k y x).mp (le_of_eq h.symm))

-- [D-1605] eq_refl_of_stageDefinable
theorem eq_refl_of_stageDefinable (hs : StageDefinable) (θ : DInfty ≃o DInfty) :
    θ = OrderIso.refl DInfty := by
  have key : ∀ (k : ℕ) (x : D k), θ (toD k x) = toD k x := by
    intro k
    choose f hf using hs θ k
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
    intro x
    rw [hf x, congrFun hid x]
    rfl
  refine RelIso.ext ?_
  intro z
  induction z using Quotient.inductionOn with
  | _ p => exact key p.1 p.2

-- [D-1606] colimit_rigid_of_stageDefinable
theorem colimit_rigid_of_stageDefinable (hs : StageDefinable) :
    Subsingleton (DInfty ≃o DInfty) :=
  ⟨fun a b => (eq_refl_of_stageDefinable hs a).trans
    (eq_refl_of_stageDefinable hs b).symm⟩

-- [D-1607] DBilimit_rigid_of_stageDefinable
theorem DBilimit_rigid_of_stageDefinable (hs : StageDefinable) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_DInfty_rigid (colimit_rigid_of_stageDefinable hs)

end Assembly
