import Dinfty.Assembly

open GluingTowerLibrary SierpinskiApplication

-- [D-1608] §The-rest-of-pillar-B-s-chain-compiled
open scoped Classical

namespace AssemblyChain

open Assembly

-- [D-1609] JoinIrredStagePreserved
def JoinIrredStagePreserved : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), JoinIrred (D k) x →
    ∃ y : D k, JoinIrred (D k) y ∧ θ (toD k x) = toD k y

-- [D-1610] StageJoinRecoverable
def StageJoinRecoverable : Prop :=
  ∀ (k : ℕ) (x : D k),
    IsLUB {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z ∧ z ≤ toD k x}
      (toD k x)

-- [D-1611] StageSupClosed
def StageSupClosed : Prop :=
  ∀ (k : ℕ) (S : Set DInfty) (z : DInfty),
    (∀ w ∈ S, ∃ y : D k, toD k y = w) → IsLUB S z → ∃ y : D k, toD k y = z

-- [D-1612] stageDefinable_of
theorem stageDefinable_of (h1 : JoinIrredStagePreserved)
    (h3 : StageJoinRecoverable) (hc : StageSupClosed) : StageDefinable := by
  intro θ k x
  have hlub : IsLUB {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z
      ∧ z ≤ toD k x} (toD k x) := h3 k x
  have himg : IsLUB (θ '' {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z
      ∧ z ≤ toD k x}) (θ (toD k x)) := (OrderIso.isLUB_image' θ).mpr hlub
  obtain ⟨y, hy⟩ := hc k _ (θ (toD k x)) (by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨y0, hy0, hy0z, -⟩ := hz
    obtain ⟨y', -, hy'eq⟩ := h1 θ k y0 hy0
    exact ⟨y', by rw [← hy0z]; exact hy'eq.symm⟩) himg
  exact ⟨y, hy.symm⟩

-- [D-1613] DBilimit_rigid_of_chain
theorem DBilimit_rigid_of_chain (h1 : JoinIrredStagePreserved)
    (h3 : StageJoinRecoverable) (hc : StageSupClosed) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_stageDefinable (stageDefinable_of h1 h3 hc)

end AssemblyChain
