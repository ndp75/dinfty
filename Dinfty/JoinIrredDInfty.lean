import Dinfty.ColimitCompatPipe

open GluingTowerLibrary SierpinskiApplication

-- [D-1630] §The-DInfty-level-half-of-clause-3b
open scoped Classical

namespace JoinIrredDInfty

open ColimitCompatPipe Assembly AssemblyChain JoinIrredLevelStable

-- [D-1631] inst-OrderBot
noncomputable instance : OrderBot DInfty where
  bot := toD 0 (⊥ : D 0)
  bot_le := toD_bot_le 0

-- [D-1632] bot_eq_toD
theorem bot_eq_toD (k : ℕ) : (⊥ : DInfty) = toD k (⊥ : D k) :=
  le_antisymm (bot_le) (toD_bot_le k _)

-- [D-1633] toD_eq_bot_iff
theorem toD_eq_bot_iff (k : ℕ) (x : D k) : toD k x = (⊥ : DInfty) ↔ x = (⊥ : D k) := by
  rw [bot_eq_toD k]
  exact ⟨fun h => toD_inj k h, fun h => by rw [h]⟩

-- [D-1634] §Order-isomorphisms-preserve-join-irreducibility
-- [D-1635] §The-DInfty-level-characterization
-- [D-1636] joinIrred_toD_iff
theorem joinIrred_toD_iff (k : ℕ) (x : D k) :
    JoinIrred DInfty (toD k x) ↔ JoinIrred (D k) x := by
  constructor
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hx => hne ((toD_eq_bot_iff k x).mpr hx), ?_⟩
    intro b c hbc
    have h' : toD k x = toD k b ⊔ toD k c := by rw [toD_sup', ← hbc]
    rcases hsplit _ _ h' with hh | hh
    · left; exact toD_inj k hh
    · right; exact toD_inj k hh
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hb => hne ((toD_eq_bot_iff k x).mp hb), ?_⟩
    intro b c hbc
    induction b using Quotient.inductionOn with
    | _ pb =>
      induction c using Quotient.inductionOn with
      | _ pc =>
        obtain ⟨p, u⟩ := pb
        obtain ⟨q, v⟩ := pc
        set N := max k (max p q) with hN
        have hkN : k ≤ N := le_max_left _ _
        have hpN : p ≤ N := le_trans (le_max_left p q) (le_max_right k _)
        have hqN : q ≤ N := le_trans (le_max_right p q) (le_max_right k _)
        have hx : toD k x = toD N (iotaLe hkN x) := (toD_iotaLe hkN x).symm
        have hu : toD p u = toD N (iotaLe hpN u) := (toD_iotaLe hpN u).symm
        have hv : toD q v = toD N (iotaLe hqN v) := (toD_iotaLe hqN v).symm
        have hjoin : toD N (iotaLe hkN x)
            = toD N (iotaLe hpN u ⊔ iotaLe hqN v) := by
          rw [← toD_sup', ← hu, ← hv, ← hx]; exact hbc
        have heq : iotaLe hkN x = iotaLe hpN u ⊔ iotaLe hqN v := toD_inj N hjoin
        have hji : JoinIrred (D N) (iotaLe hkN x) :=
          (joinIrred_iotaLe_iff hkN x).mpr ⟨hne, hsplit⟩
        rcases hji.2 _ _ heq with hh | hh
        · left
          show toD k x = toD p u
          rw [hx, hu, hh]
        · right
          show toD k x = toD q v
          rw [hx, hv, hh]

-- [D-1637] §The-residue-with-the-join-irreducibility
-- [D-1638] StageFixed
def StageFixed : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), JoinIrred (D k) x →
    ∃ y : D k, θ (toD k x) = toD k y

-- [D-1639] joinIrredStagePreserved_of_stageFixed
theorem joinIrredStagePreserved_of_stageFixed (h : StageFixed) :
    JoinIrredStagePreserved := by
  intro θ k x hx
  obtain ⟨y, hy⟩ := h θ k x hx
  refine ⟨y, ?_, hy⟩
  have h1 : JoinIrred DInfty (toD k x) := (joinIrred_toD_iff k x).mpr hx
  have h2 : JoinIrred DInfty (toD k y) := by
    rw [← hy]; exact GluingTowerLibrary.joinIrred_orderIso θ h1
  exact (joinIrred_toD_iff k y).mp h2

-- [D-1640] §colimit-compat-from-the-tightened-residue
-- [D-1641] colimit_rigid_of_stageFixed
theorem colimit_rigid_of_stageFixed (h : StageFixed) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_rigid_of_joinIrredStagePreserved (joinIrredStagePreserved_of_stageFixed h)

-- [D-1642] colimit_compat_of_stageFixed
theorem colimit_compat_of_stageFixed (h : StageFixed) :
    Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k) :=
  colimit_compat_of_joinIrredStagePreserved (joinIrredStagePreserved_of_stageFixed h)

-- [D-1643] DBilimit_rigid_of_stageFixed
theorem DBilimit_rigid_of_stageFixed (h : StageFixed) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_joinIrredStagePreserved' (joinIrredStagePreserved_of_stageFixed h)

end JoinIrredDInfty
