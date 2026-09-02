import Dinfty.StageRigidity

open GluingTowerLibrary SierpinskiApplication

-- [D-3297] §Cleaning-the-residue-PhiStageDefinable-down
open Set

open scoped Classical

namespace PhiStagePipe

open PhiIterateTower PhiBilimit EpPairTower StageRigidity BilimitGap

-- [D-3298] §0-The-stage-inclusion-with-its-domain-spelled
-- [D-3299] insD
noncomputable def insD (k : ℕ) (y : D (k + 1)) : B := phiTowerEP.ins k y

-- [D-3300] insD_le_iff
theorem insD_le_iff (k : ℕ) (a : D (k + 1)) (u : B) : insD k a ≤ u ↔ a ≤ u.1 k :=
  StageRigidity.ins_le_iff' (T := phiTowerEP) k a u

-- [D-3301] insD_monotone
theorem insD_monotone (k : ℕ) : Monotone (insD k) :=
  EpPairTower.ins_monotone (T := phiTowerEP) k

-- [D-3302] insD_le_self
theorem insD_le_self (y : B) (k : ℕ) : insD k (y.1 k) ≤ y :=
  EpPairTower.ins_le_self (T := phiTowerEP) y k

-- [D-3303] §1-The-two-routine-Props-discharged
-- [D-3304] stageSupClosed
theorem stageSupClosed (k : ℕ) (S : Set B) (z : B)
    (hS : ∀ w ∈ S, ∃ y : D (k + 1), insD k y = w) (hz : IsLUB S z) :
    ∃ y : D (k + 1), insD k y = z := by
  classical
  set T₀ : Finset (D (k + 1)) :=
    Finset.univ.filter (fun y : D (k + 1) => insD k y ∈ S) with hT₀
  refine ⟨T₀.sup id, ?_⟩
  have hlub : IsLUB S (insD k (T₀.sup id)) := by
    constructor
    · intro w hw
      obtain ⟨y, rfl⟩ := hS w hw
      exact insD_monotone k (Finset.le_sup (f := id)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hw⟩))
    · intro u hu
      refine (insD_le_iff k _ u).mpr (Finset.sup_le ?_)
      intro y hy
      have hyS : insD k y ∈ S := (Finset.mem_filter.mp hy).2
      exact (insD_le_iff k y u).mp (hu hyS)
  exact hlub.unique hz

-- [D-3305] stageJI
def stageJI (k : ℕ) (x : D (k + 1)) : Set B :=
  {z : B | ∃ y : D (k + 1), JoinIrred (D (k + 1)) y ∧ insD k y = z ∧ z ≤ insD k x}

-- [D-3306] stageJoinRecoverable
theorem stageJoinRecoverable (k : ℕ) (x : D (k + 1)) :
    IsLUB (stageJI k x) (insD k x) := by
  classical
  constructor
  · rintro z ⟨_, _, _, hle⟩
    exact hle
  · intro u hu
    refine (insD_le_iff k x u).mpr ?_
    have hx : x = (Finset.univ.filter (fun q : D (k + 1) =>
        JoinIrred (D (k + 1)) q ∧ q ≤ x)).sup id := finite_lattice_eq_sup_joinIrreds x
    rw [hx]
    refine Finset.sup_le ?_
    intro y hy
    obtain ⟨hji, hyx⟩ := (Finset.mem_filter.mp hy).2
    exact (insD_le_iff k y u).mp (hu ⟨y, hji, rfl, insD_monotone k hyx⟩)

-- [D-3307] §2-The-stages-are-exactly-the-compact-elements
-- [D-3308] insD_omegaCompact
set_option maxHeartbeats 1000000 in
theorem insD_omegaCompact (k : ℕ) (x : D (k + 1)) : OmegaCompact (insD k x) := by
  intro c hc s hs hle
  have hdir : DirectedOn (· ≤ ·) (Set.range c) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨c (max a b), ⟨max a b, rfl⟩, hc (le_max_left a b), hc (le_max_right a b)⟩
  have hlvl := EpPairTower.isLUB_bilim_apply phiTowerEP_isDcpo hs ⟨c 0, 0, rfl⟩ hdir k
  have himg : ((fun z : B => z.1 k) '' Set.range c) = Set.range fun n => (c n).1 k := by
    rw [← Set.range_comp]
    rfl
  rw [himg] at hlvl
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => (c n).1 k, fun a b hab => (hc hab) k⟩ : ℕ →o D (k + 1))
  have hub : ∀ b ∈ Set.range fun n => (c n).1 k, b ≤ (c N).1 k := by
    rintro _ ⟨m, rfl⟩
    rcases le_total N m with hle' | hle'
    · exact le_of_eq (hN m hle').symm
    · exact (hc hle') k
  have hsk : s.1 k ≤ (c N).1 k := hlvl.2 hub
  exact ⟨N, (insD_le_iff k x (c N)).mpr (((insD_le_iff k x s).mp hle).trans hsk)⟩

-- [D-3309] exists_stage_of_omegaCompact
theorem exists_stage_of_omegaCompact {z : B} (hz : OmegaCompact z) :
    ∃ (k : ℕ) (y : D (k + 1)), insD k y = z := by
  have hmono : Monotone (fun n => insD n (z.1 n)) :=
    fun a b h => EpPairTower.ins_chain_mono (T := phiTowerEP) z h
  have hlub : IsLUB (Set.range fun n => insD n (z.1 n)) z :=
    EpPairTower.chainSet_isLUB (T := phiTowerEP) z
  obtain ⟨n, hn⟩ := hz _ hmono z hlub le_rfl
  exact ⟨n, z.1 n, le_antisymm (insD_le_self z n) hn⟩

-- [D-3310] omegaCompact_iff_stage
theorem omegaCompact_iff_stage (z : B) :
    OmegaCompact z ↔ ∃ (k : ℕ) (y : D (k + 1)), insD k y = z :=
  ⟨exists_stage_of_omegaCompact, fun ⟨k, y, hy⟩ => hy ▸ insD_omegaCompact k y⟩

-- [D-3311] stages_union_preserved
theorem stages_union_preserved (θ : B ≃o B) (k : ℕ) (x : D (k + 1)) :
    ∃ (n : ℕ) (y : D (n + 1)), θ (insD k x) = insD n y := by
  obtain ⟨n, y, hy⟩ := exists_stage_of_omegaCompact ((insD_omegaCompact k x).map θ)
  exact ⟨n, y, hy.symm⟩

-- [D-3312] §3-RETIRED-the-join-irreducible-route
-- [D-3313] §4-What-the-residue-is-already-pinned
-- [D-3314] apply_insD_bot
theorem apply_insD_bot (θ : B ≃o B) (k : ℕ) : θ (insD k ⊥) = insD k ⊥ := by
  rw [show insD k (⊥ : D (k + 1)) = (⊥ : B) from PhiBilimit.ins_bot k]
  exact θ.map_bot

-- [D-3315] apply_insD_top
theorem apply_insD_top (θ : B ≃o B) (k : ℕ) : θ (insD k ⊤) = insD k ⊤ := by
  rw [show insD k (⊤ : D (k + 1)) = (⊤ : B) from PhiBilimit.ins_top k]
  exact θ.map_top

end PhiStagePipe
