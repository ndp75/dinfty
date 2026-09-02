import Dinfty.SeamCut

open GluingTowerLibrary SierpinskiApplication

-- [D-3528] §The-global-invariants-applied-to-the-seam
open scoped Classical

namespace IdealInvariant

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open SeamFixed CanonicalChain SeamCut

-- [D-3529] §1-The-invariant
-- [D-3530] idealIso
noncomputable def idealIso (θ : B ≃o B) (c : B) :
    {y : B // y ≤ c} ≃o {y : B // y ≤ θ c} where
  toFun := fun y => ⟨θ y.1, θ.monotone y.2⟩
  invFun := fun y => ⟨θ.symm y.1, by
    have h := θ.symm.monotone y.2
    rwa [OrderIso.symm_apply_apply] at h⟩
  left_inv := fun y => Subtype.ext (θ.symm_apply_apply y.1)
  right_inv := fun y => Subtype.ext (θ.apply_symm_apply y.1)
  map_rel_iff' := θ.le_iff_le

-- [D-3531] theta_cSeamB_stage
theorem theta_cSeamB_stage (θ : B ≃o B) :
    ∃ (n : ℕ) (y : D (n + 1)), θ cSeamB = insD n y := by
  have h : θ (insD 1 (cSeam 1)) = θ cSeamB := rfl
  obtain ⟨n, y, hy⟩ := PhiStagePipe.stages_union_preserved θ 1 (cSeam 1)
  exact ⟨n, y, h ▸ hy⟩

-- [D-3532] cSeamFixed_of_ideal_pins
theorem cSeamFixed_of_ideal_pins
    (h : ∀ z : B, Nonempty ({y : B // y ≤ z} ≃o {y : B // y ≤ cSeamB}) → z = cSeamB) :
    CanonicalChain.CSeamFixed := by
  intro θ
  refine h (θ cSeamB) ⟨?_⟩
  exact (idealIso θ cSeamB).symm

-- [D-3533] §2-Inside-a-level-the-invariant-decides-every
-- [D-3534] ideal_ncard_lt_of_lt
theorem ideal_ncard_lt_of_lt {k : ℕ} {z : D (k + 1)} (hz : z < cSeam k) :
    {w : D (k + 1) | w ≤ z}.ncard < {w : D (k + 1) | w ≤ cSeam k}.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨fun w hw => le_trans hw (le_of_lt hz), ?_⟩
  intro hsub
  exact absurd (hsub (le_refl (cSeam k))) (not_le_of_gt hz)

-- [D-3535] ideal_ncard_lt_of_gt
theorem ideal_ncard_lt_of_gt {k : ℕ} {z : D (k + 1)} (hz : cSeam k < z) :
    {w : D (k + 1) | w ≤ cSeam k}.ncard < {w : D (k + 1) | w ≤ z}.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨fun w hw => le_trans hw (le_of_lt hz), ?_⟩
  intro hsub
  exact absurd (hsub (le_refl z)) (not_le_of_gt hz)

-- [D-3536] not_idealIso_of_ne_of_comp
theorem not_idealIso_of_ne_of_comp {k : ℕ} {z : D (k + 1)} (hne : z ≠ cSeam k)
    (hcomp : z ≤ cSeam k ∨ cSeam k ≤ z) :
    ¬ Nonempty ({w : D (k + 1) // w ≤ z} ≃o {w : D (k + 1) // w ≤ cSeam k}) := by
  rintro ⟨e⟩
  have hcard : Nat.card {w : D (k + 1) // w ≤ z}
      = Nat.card {w : D (k + 1) // w ≤ cSeam k} := Nat.card_congr e.toEquiv
  have hz : {w : D (k + 1) | w ≤ z}.ncard = Nat.card {w : D (k + 1) // w ≤ z} := rfl
  have hs : {w : D (k + 1) | w ≤ cSeam k}.ncard
      = Nat.card {w : D (k + 1) // w ≤ cSeam k} := rfl
  rcases hcomp with hle | hge
  · have hlt : z < cSeam k := lt_of_le_of_ne hle hne
    have := ideal_ncard_lt_of_lt hlt
    rw [hz, hs, hcard] at this
    exact lt_irrefl _ this
  · have hlt : cSeam k < z := lt_of_le_of_ne hge (Ne.symm hne)
    have := ideal_ncard_lt_of_gt hlt
    rw [hz, hs, hcard] at this
    exact lt_irrefl _ this

-- [D-3537] §3-What-is-left-named
-- [D-3538] comparable_or_tagB
theorem comparable_or_tagB {k : ℕ} (z : D (k + 1)) :
    (z ≤ cSeam k ∨ cSeam k ≤ z) ∨ ∃ y : EndP (D k), z.1 = Sum.inr (Sum.inl y) := by
  rcases hz : z.1 with u | w
  · exact Or.inl (Or.inl ((mem_copyA_iff_le_cSeam k z).mp ⟨u, hz⟩))
  · rcases w with y | c
    · exact Or.inr ⟨y, rfl⟩
    · exact Or.inl (Or.inr ((cSeam_le_iff k z).mpr (Or.inr (Or.inr ⟨c, hz⟩))))

end IdealInvariant
