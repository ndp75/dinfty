import Dinfty.CanonicalChain

open GluingTowerLibrary SierpinskiApplication

-- [D-3520] §CSeamFixed-the-seam-is-a-cut-point
open scoped Classical

namespace SeamCut

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open GenContinuity SeamFixed CanonicalChain

-- [D-3521] §1-The-seam-is-the-bottom-of-copy-C
-- [D-3522] canon_tagC_bot
theorem canon_tagC_bot (k : ℕ) :
    canonGen (markedPt k) (Sum.inr (Sum.inr (⊥ : EndP (D k))))
      = Sum.inl (⊤ : EndP (D k)) := by
  rw [canonGen, if_pos rfl]

-- [D-3523] cSeam_le_iff
theorem cSeam_le_iff (k : ℕ) (z : D (k + 1)) :
    cSeam k ≤ z ↔ (z.1 = Sum.inl (⊤ : EndP (D k))
      ∨ z.1 = Sum.inr (Sum.inl (⊤ : EndP (D k)))
      ∨ ∃ c : EndP (D k), z.1 = Sum.inr (Sum.inr c)) := by
  have hnd := D_marked_point_nondegenerate k
  constructor
  · intro h
    have hle : leGlueGen (markedPt k) (Sum.inl (⊤ : EndP (D k))) z.1 := h
    rcases hz : z.1 with u | w
    · left
      rw [hz] at hle
      have hu : (⊤ : EndP (D k)) ≤ u :=
        (leGlueGen_tagA_tagA_iff (markedPt k) hnd.1 _ u).mp hle
      rw [top_le_iff.mp hu]
    · rcases w with y | c
      · rcases eq_or_ne y (⊤ : EndP (D k)) with hy | hy
        · right; left; rw [hy]
        · exfalso
          rw [hz] at hle
          exact hnd.2.1
            (top_le_iff.mp ((leGlue_tagA_tagB_iffGen (markedPt k) _ y hy).mp hle))
      · right; right; exact ⟨c, rfl⟩
  · intro h
    show leGlueGen (markedPt k) (cSeam k).1 z.1
    rw [cSeam_val]
    rcases h with h | h | ⟨c, h⟩
    · rw [h]
      exact (leGlueGen_tagA_tagA_iff (markedPt k) hnd.1 _ _).mpr (le_refl _)
    · rw [h]
      exact leGlue_tagA_tagB_topGen (markedPt k) (⊤ : EndP (D k))
    · rw [h]
      exact leGlueGen_tagA_tagC (markedPt k) _ c

-- [D-3524] §2-Fixing-the-seam-preserving-the-copy-A-ideal
-- [D-3525] cSeamFixed_iff_ideal_stable
theorem cSeamFixed_iff_ideal_stable :
    CanonicalChain.CSeamFixed ↔ ∀ (θ : B ≃o B) (y : B), y ≤ cSeamB ↔ θ y ≤ cSeamB := by
  constructor
  · intro h θ y
    constructor
    · intro hy
      rw [← h θ]
      exact θ.monotone hy
    · intro hy
      rw [← h θ] at hy
      exact θ.le_iff_le.mp hy
  · intro h θ
    have h1 : θ cSeamB ≤ cSeamB := (h θ cSeamB).mp (le_refl _)
    have h2 : cSeamB ≤ θ cSeamB := by
      have h3 : θ.symm cSeamB ≤ cSeamB := by
        have := (h θ (θ.symm cSeamB)).mpr (by rw [OrderIso.apply_symm_apply])
        exact this
      have h4 := θ.monotone h3
      rwa [OrderIso.apply_symm_apply] at h4
    exact le_antisymm h1 h2

-- [D-3526] §3-Why-the-local-handles-fail
-- [D-3527] spikeHom_lamD_le
theorem spikeHom_lamD_le (k : ℕ) (u : EndP (D k)) (hu : u ≠ ⊥) :
    spikeHom (TowerNoAbsorption.lamD k) ≤ u := by
  have hut : u ⊤ ≠ (⊥ : D k) := fun hc => hu (AtomlessBilimit.eq_bot_of_apply_top hc)
  rw [OrderHom.le_def]
  intro x
  rcases eq_or_ne x (⊤ : D k) with hx | hx
  · subst hx
    rw [spikeHom_apply_top]
    exact TowerNoAbsorption.lamD_le k _ hut
  · rw [spikeHom_apply_of_ne _ hx]
    exact bot_le

end SeamCut
