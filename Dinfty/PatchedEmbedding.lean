import Dinfty.EmbTagwise
import Dinfty.ColimitCompatPipe

open GluingTowerLibrary SierpinskiApplication

-- [D-3452] §LevelEmbUnique-is-FALSE-and-obstruction-T
open scoped Classical

namespace PatchedEmbedding

open PhiIterateTower

-- [D-3453] §1-is-join-irreducible-at-every-level
-- [D-3454] top_joinIrred
theorem top_joinIrred (k : ℕ) {x y : D k} (h : x ⊔ y = (⊤ : D k)) :
    x = ⊤ ∨ y = ⊤ := by
  letI := realUniqueAtomCoatom k
  by_contra hc
  push_neg at hc
  have hx : x ≤ coatomOf (D k) := coatomOf_le hc.1
  have hy : y ≤ coatomOf (D k) := coatomOf_le hc.2
  have : (⊤ : D k) ≤ coatomOf (D k) := h ▸ sup_le hx hy
  exact coatomOf_ne_top (D k) (top_le_iff.mp this)

-- [D-3455] §2-The-patched-inclusion
-- [D-3456] patched
noncomputable def patched (k : ℕ) (x : D (k + 1)) : D (k + 2) :=
  if x = ⊤ then ⊤ else iotaD (k + 1) x

-- [D-3457] patched_of_ne_top
theorem patched_of_ne_top {k : ℕ} {x : D (k + 1)} (hx : x ≠ ⊤) :
    patched k x = iotaD (k + 1) x := if_neg hx

-- [D-3458] patched_top
@[simp] theorem patched_top (k : ℕ) : patched k (⊤ : D (k + 1)) = ⊤ := if_pos rfl

-- [D-3459] patched_bot
theorem patched_bot (k : ℕ) : patched k (⊥ : D (k + 1)) = (⊥ : D (k + 2)) := by
  have hbt : (⊥ : D (k + 1)) ≠ (⊤ : D (k + 1)) := bot_ne_top_of_nontrivial
  rw [patched_of_ne_top hbt]
  exact ColimitCompatPipe.iotaD_bot (k + 1)

-- [D-3460] patched_monotone
theorem patched_monotone (k : ℕ) : Monotone (patched k) := by
  intro x y hxy
  by_cases hy : y = ⊤
  · rw [hy, patched_top]; exact le_top
  · have hx : x ≠ ⊤ := fun hc => hy (top_le_iff.mp (hc ▸ hxy))
    rw [patched_of_ne_top hx, patched_of_ne_top hy]
    exact iotaD_monotone (k + 1) hxy

-- [D-3461] patched_reflect
set_option maxHeartbeats 1000000 in
theorem patched_reflect (k : ℕ) (x y : D (k + 1)) (h : patched k x ≤ patched k y) :
    x ≤ y := by
  by_cases hy : y = ⊤
  · rw [hy]; exact le_top
  · by_cases hx : x = ⊤
    · exfalso
      have h1 : (⊤ : D (k + 2)) ≤ iotaD (k + 1) y := by
        rw [← patched_top (k := k), ← hx, ← patched_of_ne_top hy]
        exact h
      exact iotaD_ne_top (k + 1) y (top_le_iff.mp h1)
    · have h2 : iotaD (k + 1) x ≤ iotaD (k + 1) y := by
        rw [← patched_of_ne_top hx, ← patched_of_ne_top hy]
        exact h
      exact (iotaD_le_iff (k + 1) x y).mp h2

-- [D-3462] patched_sup
theorem patched_sup (k : ℕ) (x y : D (k + 1)) :
    patched k (x ⊔ y) = patched k x ⊔ patched k y := by
  by_cases hx : x = ⊤
  · subst hx
    rw [top_sup_eq, patched_top, top_sup_eq]
  by_cases hy : y = ⊤
  · subst hy
    rw [sup_top_eq, patched_top, sup_top_eq]
  have hxy : x ⊔ y ≠ ⊤ := fun hc => (top_joinIrred (k + 1) hc).elim hx hy
  rw [patched_of_ne_top hx, patched_of_ne_top hy, patched_of_ne_top hxy]
  exact (iotaD_sup (k + 1) x y).symm

-- [D-3463] §3-It-is-not-the-canonical-embedding
-- [D-3464] patched_val_ne_top
theorem patched_val_ne_top {k : ℕ} {x : D (k + 1)} (hx : x ≠ ⊤) :
    ∃ a : EndP (D (k + 1)), (patched k x).1 = Sum.inl a := by
  rw [patched_of_ne_top hx]
  exact ⟨constHom x, rfl⟩

-- [D-3465] §4-The-refutation
open CopyHierarchy

-- [D-3466] hmt1
private theorem hmt1 : (markedPt 1) ≠ ⊤ := (D_marked_point_nondegenerate 1).2.1
-- [D-3467] hbt1
private theorem hbt1 : (⊥ : EndP (D 1)) ≠ ⊤ := (D_marked_point_nondegenerate 1).2.2

-- [D-3468] top_val_two
theorem top_val_two : (⊤ : D 2).1 = Sum.inr (Sum.inr (⊤ : EndP (D 1))) := by
  show canonGen (markedPt 1) (Sum.inr (Sum.inr (⊤ : EndP (D 1)))) = _
  rw [canonGen, if_neg (Ne.symm hbt1), if_neg (Ne.symm hmt1)]

-- [D-3469] wB
noncomputable def wB : D 2 := glueB (markedPt 1) (⊤ : EndP (D 1)) (Ne.symm hbt1)

-- [D-3470] wB_val
theorem wB_val : wB.1 = Sum.inr (Sum.inl (⊤ : EndP (D 1))) := rfl

-- [D-3471] wB_ne_top
theorem wB_ne_top : wB ≠ (⊤ : D 2) := by
  intro h
  have hv := congrArg Subtype.val h
  rw [wB_val, top_val_two] at hv
  exact Sum.inl_ne_inr (Sum.inr_injective hv)

-- [D-3472] copyIdx_wB
theorem copyIdx_wB : copyIdx wB.1 = 1 := by rw [wB_val]; rfl

-- [D-3473] not_levelEmbUnique
theorem not_levelEmbUnique : ¬ StageEmbedding.LevelEmbUnique := by
  intro h
  have hle : (1 : ℕ) ≤ 2 := by norm_num
  have hf : patched 1 = StageEmbedding.embD hle :=
    h 1 2 hle (patched 1) (patched_monotone 1) (patched_reflect 1)
      (patched_bot 1) (patched_top 1) (patched_sup 1)
  have hA : copyIdx (patched 1 wB).1 = 0 := by
    obtain ⟨a, ha⟩ := patched_val_ne_top wB_ne_top
    rw [ha]; rfl
  have hB : copyIdx (StageEmbedding.embD hle wB).1 = 1 := by
    have hemb : StageEmbedding.embD hle wB = (iter 1).emb wB := by
      show phiTowerEP.embLe hle wB = _
      rw [EpPairTower.embLe_succ (T := phiTowerEP) (le_refl 1) hle wB,
        EpPairTower.embLe_self (T := phiTowerEP) (le_refl 1) wB]
      rfl
    rw [hemb, EmbTagwise.emb_succ_copyIdx 0 wB]
    exact copyIdx_wB
  rw [hf, hB] at hA
  exact absurd hA (by decide)

-- [D-3474] not_levelImageStable
theorem not_levelImageStable : ¬ EmbDImage.LevelImageStable := fun h =>
  not_levelEmbUnique (EmbDImage.levelEmbUnique_of_levelImageStable h)

-- [D-3475] not_levelImageStableJI
theorem not_levelImageStableJI : ¬ EmbDImage.LevelImageStableJI := fun h =>
  not_levelImageStable (EmbDImage.levelImageStable_of_JI h)

end PatchedEmbedding
