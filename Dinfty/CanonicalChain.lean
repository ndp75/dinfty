import Dinfty.StageCover
import Dinfty.SeamFixed

open GluingTowerLibrary SierpinskiApplication

-- [D-3488] §Splitting-again-the-canonical-chain
open scoped Classical

namespace CanonicalChain

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open StageCofinal PatchedEmbedding AtomlessBilimit StageCover SeamFixed

-- [D-3489] §0-Two-spellings-the-tower-needs
-- [D-3490] top_val_succ
theorem top_val_succ (k : ℕ) :
    ((⊤ : D (k + 1))).1 = Sum.inr (Sum.inr (⊤ : EndP (D k))) := by
  have hnd := D_marked_point_nondegenerate k
  show canonGen (markedPt k) (Sum.inr (Sum.inr (⊤ : EndP (D k)))) = _
  rw [canonGen, if_neg (Ne.symm hnd.2.2), if_neg (Ne.symm hnd.2.1)]

-- [D-3491] cSeam_ne_top
theorem cSeam_ne_top (k : ℕ) : cSeam k ≠ (⊤ : D (k + 1)) := by
  intro h
  have h1 : (cSeam k).1 = ((⊤ : D (k + 1))).1 := congrArg Subtype.val h
  rw [cSeam_val, top_val_succ k] at h1
  exact Sum.inl_ne_inr h1

-- [D-3492] insD_emb
theorem insD_emb (n : ℕ) (y : D (n + 1)) :
    insD (n + 1) ((iter n).emb y) = insD n y := by
  have hembLe : phiTowerEP.embLe (Nat.le_succ n) y = (iter n).emb y := by
    rw [EpPairTower.embLe_succ (T := phiTowerEP) (le_refl n) (Nat.le_succ n) y,
      EpPairTower.embLe_self (T := phiTowerEP) (le_refl n) y]
    rfl
  show phiTowerEP.ins (n + 1) ((iter n).emb y) = phiTowerEP.ins n y
  rw [← hembLe]
  exact EpPairTower.ins_embLe (T := phiTowerEP) (Nat.le_succ n) y

-- [D-3493] §1-The-seam-is-level-stable-above-the-base
-- [D-3494] endUpFun_top
theorem endUpFun_top {k : ℕ} (E : TriEP k) :
    E.endUpFun (⊤ : EndP (D k)) = (⊤ : EndP (D (k + 1))) := E.endUp.map_top

-- [D-3495] emb_cSeam_succ
theorem emb_cSeam_succ (n : ℕ) :
    (iter (n + 1)).emb (cSeam (n + 1)) = cSeam (n + 2) := by
  show (iter (n + 1)).emb (glueA (markedPt (n + 1)) (⊤ : EndP (D (n + 1))))
    = glueA (markedPt (n + 2)) (⊤ : EndP (D (n + 2)))
  rw [AtomlessBilimit.emb_succ_glueA (n) (⊤ : EndP (D (n + 1))), endUpFun_top (iter n)]

-- [D-3496] base_emb_cSeam_ne
theorem base_emb_cSeam_ne : (iter 0).emb (cSeam 0) ≠ cSeam 1 := by
  intro hcon
  have h1 : glueAA 0 (glueA (markedPt 0) (⊤ : EndP (D 0)))
      = glueA (markedPt 1) (iotaEndP 0 (⊤ : EndP (D 0))) :=
    GlueAAJoin.glueAA_glueA 0 (⊤ : EndP (D 0))
  rw [show (iter 0).emb = glueAA 0 from rfl, show cSeam 0
    = glueA (markedPt 0) (⊤ : EndP (D 0)) from rfl, h1,
    show cSeam 1 = glueA (markedPt 1) (⊤ : EndP (D 1)) from rfl] at hcon
  have h2 : iotaEndP 0 (⊤ : EndP (D 0)) = (⊤ : EndP (D 1)) :=
    glueA_injective (markedPt 1) hcon
  have h3 : (iotaEndP 0 (⊤ : EndP (D 0))) (⊥ : D 1) = (⊤ : EndP (D 1)) (⊥ : D 1) :=
    congrArg (fun g : EndP (D 1) => g ⊥) h2
  rw [endPTop_apply] at h3
  exact iotaD_ne_top 0 ((⊤ : EndP (D 0)) (pD 0 (⊥ : D 1))) h3

-- [D-3497] §2-The-canonical-point
-- [D-3498] cSeamB
noncomputable def cSeamB : B := insD 1 (cSeam 1)

-- [D-3499] insD_cSeam
theorem insD_cSeam : ∀ n : ℕ, insD (n + 1) (cSeam (n + 1)) = cSeamB
  | 0 => rfl
  | n + 1 => by
      rw [← emb_cSeam_succ n, insD_emb (n + 1) (cSeam (n + 1))]
      exact insD_cSeam n

-- [D-3500] §3-The-chain
-- [D-3501] midB_lt_cSeamB
theorem midB_lt_cSeamB : midB < cSeamB := by
  have hnd := D_marked_point_nondegenerate 1
  have hmid : midB = insD 1 (dMid 2) := (PhiBilimit.ins_mid 1).symm
  have hd : dMid 2 = glueA (markedPt 1) (markedPt 1) := rfl
  rw [hmid, hd, cSeamB, show cSeam 1 = glueA (markedPt 1) (⊤ : EndP (D 1)) from rfl]
  refine lt_of_le_of_ne (insD_monotone 1 ((glueA_le_iff (markedPt 1) hnd.1 _ _).mpr le_top)) ?_
  intro hc
  exact hnd.2.1 (glueA_injective (markedPt 1) (insD_injective 1 hc))

-- [D-3502] cSeamB_lt_top
theorem cSeamB_lt_top : cSeamB < (⊤ : B) := by
  refine lt_of_le_of_ne le_top ?_
  intro hc
  refine cSeam_ne_top 1 (insD_injective 1 ?_)
  rw [insD_top 1]
  exact hc

-- [D-3503] le_cSeamB_iff
theorem le_cSeamB_iff (n : ℕ) (x : D (n + 2)) :
    insD (n + 1) x ≤ cSeamB ↔ ∃ a : EndP (D (n + 1)), x.1 = Sum.inl a := by
  rw [← insD_cSeam n, insD_le_insD_iff]
  exact (mem_copyA_iff_le_cSeam (n + 1) x).symm

-- [D-3504] §4-The-seam-discriminates-where-the-mid-does-not
-- [D-3505] iotaD_preserves_mid
theorem iotaD_preserves_mid (k : ℕ) : iotaD k (dMid k) = dMid (k + 1) := rfl

-- [D-3506] patched_ne_cSeam
theorem patched_ne_cSeam (k : ℕ) : patched k (cSeam k) ≠ cSeam (k + 1) := by
  intro hcon
  rw [patched_of_ne_top (cSeam_ne_top k)] at hcon
  have h1 : glueA (markedPt (k + 1)) (constHom (cSeam k))
      = glueA (markedPt (k + 1)) (⊤ : EndP (D (k + 1))) := hcon
  have h2 : constHom (cSeam k) = (⊤ : EndP (D (k + 1))) :=
    glueA_injective (markedPt (k + 1)) h1
  have h3 : (constHom (cSeam k) : EndP (D (k + 1))) (⊥ : D (k + 1))
      = (⊤ : EndP (D (k + 1))) (⊥ : D (k + 1)) :=
    congrArg (fun g : EndP (D (k + 1)) => g ⊥) h2
  rw [endPTop_apply] at h3
  exact cSeam_ne_top k h3

-- [D-3507] CSeamFixed
def CSeamFixed : Prop := ∀ θ : B ≃o B, θ cSeamB = cSeamB

end CanonicalChain
