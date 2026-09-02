import Dinfty.PatchedEmbedding
import Dinfty.StageCofinal
import Dinfty.AtomlessBilimit

open GluingTowerLibrary SierpinskiApplication

-- [D-3476] §Hunting-the-automorphism-instead
open scoped Classical

namespace StageCover

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open StageCofinal PatchedEmbedding AtomlessBilimit CopyHierarchy

-- [D-3477] §1-endUpFun-transports-constants
-- [D-3478] endUpFun_constHom
theorem endUpFun_constHom {k : ℕ} (E : TriEP k) (x : D k) :
    E.endUpFun (constHom x) = constHom (E.emb x) := by
  apply OrderHom.ext
  funext w
  show E.emb ((constHom x) (E.prj w)) = constHom (E.emb x) w
  rfl

-- [D-3479] emb_eq_top_iff
theorem emb_eq_top_iff {k : ℕ} (E : TriEP k) (x : D k) : E.emb x = ⊤ ↔ x = ⊤ := by
  constructor
  · intro h
    have h1 := E.retraction x
    rw [h, E.prj_top] at h1
    exact h1.symm
  · rintro rfl
    exact E.emb_top

-- [D-3480] §2-patched-is-coherent-with-the-tower
-- [D-3481] patched_coherent
theorem patched_coherent (k : ℕ) (x : D (k + 1)) :
    (iter (k + 1)).emb (patched k x) = patched (k + 1) ((iter k).emb x) := by
  rcases eq_or_ne x (⊤ : D (k + 1)) with hx | hx
  · subst hx
    rw [patched_top, (iter (k + 1)).emb_top, (iter k).emb_top, patched_top]
  · have hex : (iter k).emb x ≠ ⊤ := fun hc => hx ((emb_eq_top_iff (iter k) x).mp hc)
    rw [patched_of_ne_top hx, patched_of_ne_top hex]
    show (iter (k + 1)).emb (glueA (markedPt (k + 1)) (constHom x))
      = glueA (markedPt (k + 2)) (constHom ((iter k).emb x))
    rw [AtomlessBilimit.emb_succ_glueA k (constHom x), endUpFun_constHom (iter k) x]

-- [D-3482] §3-The-tower-s-embeddings-preserve-the-copy-index
-- [D-3483] embD_copyIdx
theorem embD_copyIdx : ∀ (m : ℕ) (h : 1 ≤ m) (y : D 2),
    copyIdx (embD h y).1 = copyIdx y.1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro h y
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · have hn : n = 0 := by omega
        subst hn
        show copyIdx (phiTowerEP.embLe h y).1 = _
        rw [EpPairTower.embLe_self (T := phiTowerEP) h y]
      · have h1 : (1 : ℕ) ≤ n := by omega
        obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
        show copyIdx (phiTowerEP.embLe h y).1 = _
        rw [EpPairTower.embLe_succ (T := phiTowerEP) h1 h y]
        show copyIdx ((iter (p + 1)).emb (phiTowerEP.embLe h1 y)).1 = _
        rw [EmbTagwise.emb_succ_copyIdx p _]
        exact ih h1 y

-- [D-3484] §4-The-stage-maps-of-an-automorphism-cover
-- [D-3485] stage_map_covers
theorem stage_map_covers (θ : B ≃o B) (y : D 2) :
    ∃ (m : ℕ) (h : 1 ≤ m + 1) (z : D (m + 1)) (m'' : ℕ) (hm : m ≤ m'')
      (f : D (m + 1) → D (m'' + 1)),
      IsStageMap θ m m'' f ∧ insD m'' (f z) = insD (m + 1) (embD h y) := by
  obtain ⟨m, hm1, g, hg⟩ := stage_map_exists' θ.symm 1
  obtain ⟨m'', hmm, f, hf⟩ := stage_map_exists' θ m
  refine ⟨m, by omega, g y, m'', hmm, f, hf, ?_⟩
  rw [← hf (g y), ← hg y, OrderIso.apply_symm_apply]
  exact (insD_embD (by omega : (1 : ℕ) ≤ m + 1) y).symm

-- [D-3486] §5-The-verdict-the-117-freedom-is-not-invertible
-- [D-3487] no_patched_automorphism
theorem no_patched_automorphism :
    ¬ ∃ θ : B ≃o B, ∀ (k : ℕ) (x : D (k + 1)), θ (insD k x) = insD (k + 1) (patched k x) := by
  rintro ⟨θ, hθ⟩
  obtain ⟨m, hm1, g, hg⟩ := stage_map_exists' θ.symm 1
  have hkey : insD (m + 1) (patched m (g wB)) = insD (m + 1) (embD (by omega : (1:ℕ) ≤ m + 1) wB) := by
    rw [← hθ m (g wB), ← hg wB, OrderIso.apply_symm_apply,
      insD_embD (by omega : (1:ℕ) ≤ m + 1) wB]
  have heq : patched m (g wB) = embD (by omega : (1:ℕ) ≤ m + 1) wB :=
    insD_injective (m + 1) hkey
  rcases eq_or_ne (g wB) (⊤ : D (m + 1)) with hgt | hgt
  ·
    rw [hgt, patched_top] at heq
    refine wB_ne_top ?_
    refine insD_injective 1 ?_
    rw [← insD_embD (by omega : (1:ℕ) ≤ m + 1) wB, ← heq, insD_top (m + 1), insD_top 1]
  ·
    obtain ⟨a, ha⟩ := patched_val_ne_top hgt
    have h0 : copyIdx (patched m (g wB)).1 = 0 := by rw [ha]; rfl
    rw [heq, embD_copyIdx (m + 1) (by omega) wB, copyIdx_wB] at h0
    exact absurd h0 (by decide)

end StageCover
