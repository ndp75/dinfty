import Dinfty.JoinIrredDInfty

open GluingTowerLibrary SierpinskiApplication

-- [D-1644] §Distance-to-D-0-has-no-foothold-at-either-end
open scoped Classical

namespace DInftyNoFootholds

open JoinIrredDInfty ColimitCompatPipe Assembly

-- [D-1645] §The-spike
-- [D-1646] spike
noncomputable def spike (k : ℕ) (x : D k) : EndP (D k) :=
  ⟨fun t => if t = (⊤ : D k) then x else (⊥ : D k), by
    intro a b hab
    dsimp only
    by_cases ha : a = (⊤ : D k)
    · have hb : b = (⊤ : D k) := le_antisymm le_top (ha ▸ hab)
      rw [if_pos ha, if_pos hb]
    · rw [if_neg ha]; exact bot_le⟩

-- [D-1647] spike_apply_top
@[simp] theorem spike_apply_top (k : ℕ) (x : D k) : spike k x (⊤ : D k) = x := by
  show (if (⊤ : D k) = (⊤ : D k) then x else ⊥) = x
  rw [if_pos rfl]

-- [D-1648] spike_apply_bot
theorem spike_apply_bot (k : ℕ) (x : D k) : spike k x (⊥ : D k) = (⊥ : D k) := by
  show (if (⊥ : D k) = (⊤ : D k) then x else ⊥) = ⊥
  rw [if_neg bot_ne_top_of_nontrivial]

-- [D-1649] spike_le_constHom
theorem spike_le_constHom (k : ℕ) (x : D k) : spike k x ≤ (constHom x : EndP (D k)) := by
  rw [OrderHom.le_def]
  intro t
  rw [constHom_apply]
  show (if t = (⊤ : D k) then x else ⊥) ≤ x
  split_ifs with h
  · exact le_rfl
  · exact bot_le

-- [D-1650] spike_ne_bot
theorem spike_ne_bot (k : ℕ) {x : D k} (hx : x ≠ (⊥ : D k)) :
    spike k x ≠ (⊥ : EndP (D k)) := by
  intro h
  have := congrArg (fun f : EndP (D k) => f (⊤ : D k)) h
  rw [spike_apply_top] at this
  exact hx this

-- [D-1651] spike_ne_constHom
theorem spike_ne_constHom (k : ℕ) {x : D k} (hx : x ≠ (⊥ : D k)) :
    spike k x ≠ (constHom x : EndP (D k)) := by
  intro h
  have := congrArg (fun f : EndP (D k) => f (⊥ : D k)) h
  rw [spike_apply_bot, constHom_apply] at this
  exact hx this.symm

-- [D-1652] §Atomlessness
-- [D-1653] exists_lt_lt_of_ne_bot
theorem exists_lt_lt_of_ne_bot {z : DInfty} (hz : z ≠ (⊥ : DInfty)) :
    ∃ w : DInfty, (⊥ : DInfty) < w ∧ w < z := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    have hx : x ≠ (⊥ : D k) := fun h => hz (by
      rw [show (Quotient.mk dInftySetoid (⟨k, x⟩ : Σ n, D n)) = toD k x from rfl, h]
      exact (bot_eq_toD k).symm)
    have hnd := D_marked_point_nondegenerate k
    refine ⟨toD (k + 1) (glueA (markedPt k) (spike k x)), ?_, ?_⟩
    ·
      rw [bot_eq_toD (k + 1)]
      refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr bot_le) ?_
      intro hcon
      exact spike_ne_bot k hx
        (glueA_injective (markedPt k)
          ((glueA_bot (markedPt k) hnd.1 hnd.2.1 hnd.2.2).trans
            (toD_inj (k + 1) hcon))).symm
    · show toD (k + 1) (glueA (markedPt k) (spike k x)) < toD k x
      rw [← toD_iotaD k x]
      refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr ?_) ?_
      · exact (glueA_le_iff (markedPt k) hnd.1 _ _).mpr (spike_le_constHom k x)
      · intro hcon
        exact spike_ne_constHom k hx
          (glueA_injective (markedPt k) (toD_inj (k + 1) hcon))

-- [D-1654] no_isAtom
theorem no_isAtom (a : DInfty) : ¬ IsAtom a := by
  rintro ⟨hne, hmin⟩
  obtain ⟨w, hw0, hwa⟩ := exists_lt_lt_of_ne_bot hne
  exact absurd (hmin w hwa) (ne_of_gt hw0)

-- [D-1655] §No-top
-- [D-1656] no_top
theorem no_top (z : DInfty) : ∃ w : DInfty, z < w := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    refine ⟨toD (k + 1) (⊤ : D (k + 1)), ?_⟩
    show toD k x < toD (k + 1) (⊤ : D (k + 1))
    rw [← toD_iotaD k x]
    refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr le_top) ?_
    intro hcon
    exact iotaD_ne_top k x (toD_inj (k + 1) hcon)

-- [D-1657] no_footholds
theorem no_footholds :
    (∀ a : DInfty, ¬ IsAtom a) ∧ (∀ z : DInfty, ∃ w : DInfty, z < w) :=
  ⟨no_isAtom, no_top⟩

end DInftyNoFootholds
