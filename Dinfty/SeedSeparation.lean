import Dinfty.Definability

open GluingTowerLibrary SierpinskiApplication

-- [D-1732] §The-search-written-into-Lean
open scoped Classical

namespace SeedSeparation

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

-- [D-1733] §The-seed-in-colimit-form
-- [D-1734] JBelow
def JBelow (z : DInfty) : Type := {w : DInfty // JoinIrred DInfty w ∧ w ≤ z}

-- [D-1735] inst-DInfty
noncomputable instance (z : DInfty) : PartialOrder (JBelow z) := Subtype.partialOrder _

-- [D-1736] JBelow.map
noncomputable def JBelow.map (θ : DInfty ≃o DInfty) (z : DInfty) :
    JBelow z ≃o JBelow (θ z) where
  toFun w := ⟨θ w.1, GluingTowerLibrary.joinIrred_orderIso θ w.2.1, θ.monotone w.2.2⟩
  invFun w := ⟨θ.symm w.1, GluingTowerLibrary.joinIrred_orderIso θ.symm w.2.1, by
    have h := θ.symm.monotone w.2.2
    rwa [θ.symm_apply_apply] at h⟩
  left_inv w := Subtype.ext (θ.symm_apply_apply w.1)
  right_inv w := Subtype.ext (θ.apply_symm_apply w.1)
  map_rel_iff' := θ.map_rel_iff

-- [D-1737] §Every-element-lies-in-a-stage
-- [D-1738] exists_stage
theorem exists_stage (w : DInfty) : ∃ (N : ℕ) (y : D N), w = toD N y := by
  induction w using Quotient.inductionOn with
  | _ p => obtain ⟨N, y⟩ := p; exact ⟨N, y, rfl⟩

-- [D-1739] §The-hypothesis-the-search-instantiates
-- [D-1740] SeedSeparatesAt
def SeedSeparatesAt (z : DInfty) (N : ℕ) : Prop :=
  ∀ y : D N, Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z

-- [D-1741] fixed_of_seedSeparates
theorem fixed_of_seedSeparates {z : DInfty} (h : ∀ N, SeedSeparatesAt z N)
    (θ : DInfty ≃o DInfty) : θ z = z := by
  obtain ⟨N, y, hy⟩ := exists_stage (θ z)
  have h0 : Nonempty (JBelow z ≃o JBelow (θ z)) := ⟨JBelow.map θ z⟩
  rw [hy] at h0
  rw [hy]
  exact h N y ⟨h0.some.symm⟩

-- [D-1742] twoPointFixed_of_seedSeparates
theorem twoPointFixed_of_seedSeparates
    (hm : ∀ N, SeedSeparatesAt midInf N)
    (ht : ∀ N, SeedSeparatesAt (toD 0 (⊤ : D 0)) N) : TwoPointFixed :=
  fun θ => ⟨fixed_of_seedSeparates hm θ, fixed_of_seedSeparates ht θ⟩

-- [D-1743] §The-part-of-the-search-Lean-can-replay
-- [D-1744] jBelow_bot_isEmpty
theorem jBelow_bot_isEmpty : IsEmpty (JBelow (⊥ : DInfty)) := by
  refine ⟨?_⟩
  rintro ⟨w, hji, hle⟩
  exact hji.1 (le_bot_iff.mp hle)

-- [D-1745] jBelow_nonempty_of_joinIrred
theorem jBelow_nonempty_of_joinIrred {z : DInfty} (hz : JoinIrred DInfty z) :
    Nonempty (JBelow z) := ⟨⟨z, hz, le_rfl⟩⟩

-- [D-1746] bot_ne_of_seed_iso
theorem bot_ne_of_seed_iso {z : DInfty} (hz : JoinIrred DInfty z)
    (_e : JBelow (⊥ : DInfty) ≃o JBelow z) : False :=
  (jBelow_bot_isEmpty).elim (_e.symm (jBelow_nonempty_of_joinIrred hz).some)

-- [D-1747] bot_ne_midInf_seed
theorem bot_ne_midInf_seed (e : JBelow (⊥ : DInfty) ≃o JBelow midInf) : False :=
  bot_ne_of_seed_iso joinIrred_midInf e

-- [D-1748] bot_ne_topJ_seed
theorem bot_ne_topJ_seed (e : JBelow (⊥ : DInfty) ≃o JBelow (toD 0 (⊤ : D 0))) : False :=
  bot_ne_of_seed_iso joinIrred_toD_zero_top e

end SeedSeparation
