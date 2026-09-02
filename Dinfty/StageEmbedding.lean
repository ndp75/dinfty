import Dinfty.PhiStagePipe

open GluingTowerLibrary SierpinskiApplication

-- [D-3316] §What-an-automorphism-of-B-looks-like-on-a-stage
open Set

open scoped Classical

namespace StageEmbedding

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe

-- [D-3317] §1-The-stage-is-a-bounded-sub-join-semilattice
-- [D-3318] insD_le_insD_iff
theorem insD_le_insD_iff (k : ℕ) (a b : D (k + 1)) : insD k a ≤ insD k b ↔ a ≤ b :=
  StageRigidity.ins_le_iff (T := phiTowerEP) k a b

-- [D-3319] insD_injective
theorem insD_injective (k : ℕ) : Function.Injective (insD k) :=
  StageRigidity.ins_injective (T := phiTowerEP) k

-- [D-3320] insD_bot
theorem insD_bot (k : ℕ) : insD k (⊥ : D (k + 1)) = (⊥ : B) := PhiBilimit.ins_bot k

-- [D-3321] insD_top
theorem insD_top (k : ℕ) : insD k (⊤ : D (k + 1)) = (⊤ : B) := PhiBilimit.ins_top k

-- [D-3322] embD
noncomputable def embD {k m : ℕ} (h : k ≤ m) (a : D (k + 1)) : D (m + 1) :=
  phiTowerEP.embLe h a

-- [D-3323] insD_embD
theorem insD_embD {k m : ℕ} (h : k ≤ m) (a : D (k + 1)) : insD m (embD h a) = insD k a :=
  EpPairTower.ins_embLe (T := phiTowerEP) h a

-- [D-3324] insD_isLUB_pair
theorem insD_isLUB_pair (k : ℕ) (a b : D (k + 1)) :
    IsLUB {insD k a, insD k b} (insD k (a ⊔ b)) := by
  constructor
  · rintro z (rfl | rfl)
    · exact insD_monotone k le_sup_left
    · exact insD_monotone k le_sup_right
  · intro u hu
    refine (insD_le_iff k _ u).mpr (sup_le ?_ ?_)
    · exact (insD_le_iff k a u).mp (hu (Set.mem_insert _ _))
    · exact (insD_le_iff k b u).mp (hu (Set.mem_insert_of_mem _ rfl))

-- [D-3325] embD_sup
theorem embD_sup {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    embD h (a ⊔ b) = embD h a ⊔ embD h b := by
  refine insD_injective m ?_
  have hL := insD_isLUB_pair m (embD h a) (embD h b)
  rw [insD_embD h a, insD_embD h b] at hL
  rw [insD_embD h (a ⊔ b)]
  exact (insD_isLUB_pair k a b).unique hL

-- [D-3326] §2-The-stage-map-of-an-automorphism
-- [D-3327] stage_map_exists
theorem stage_map_exists (θ : B ≃o B) (k : ℕ) :
    ∃ m : ℕ, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1),
      (∀ x, θ (insD k x) = insD m (f x))
        ∧ Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b)
        ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧ (∀ a b, f (a ⊔ b) = f a ⊔ f b) := by
  classical
  choose nf yf hyf using stages_union_preserved θ k
  set m : ℕ := max k (Finset.univ.sup nf) with hm
  have hnm : ∀ x : D (k + 1), nf x ≤ m := fun x =>
    le_trans (Finset.le_sup (f := nf) (Finset.mem_univ x)) (le_max_right _ _)
  obtain ⟨f, hdef⟩ : ∃ f : D (k + 1) → D (m + 1), ∀ x, θ (insD k x) = insD m (f x) := by
    refine ⟨fun x => embD (hnm x) (yf x), fun x => ?_⟩
    rw [hyf x]
    exact (insD_embD (hnm x) (yf x)).symm
  refine ⟨m, le_max_left _ _, f, hdef, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a b hab
    refine (insD_le_insD_iff m _ _).mp ?_
    rw [← hdef a, ← hdef b]
    exact θ.monotone ((insD_le_insD_iff k a b).mpr hab)
  ·
    intro a b hab
    have h1 : θ (insD k a) ≤ θ (insD k b) := by
      rw [hdef a, hdef b]
      exact insD_monotone m hab
    exact (insD_le_insD_iff k a b).mp (θ.le_iff_le.mp h1)
  ·
    refine insD_injective m ?_
    rw [← hdef ⊥, insD_bot k, insD_bot m]
    exact θ.map_bot
  ·
    refine insD_injective m ?_
    rw [← hdef ⊤, insD_top k, insD_top m]
    exact θ.map_top
  ·
    intro a b
    refine insD_injective m ?_
    have himg : IsLUB (θ '' {insD k a, insD k b}) (θ (insD k (a ⊔ b))) :=
      (OrderIso.isLUB_image' θ).mpr (insD_isLUB_pair k a b)
    rw [Set.image_pair, hdef a, hdef b, hdef (a ⊔ b)] at himg
    exact himg.unique (insD_isLUB_pair m _ _)

-- [D-3328] stage_map_comp
theorem stage_map_comp (θ : B ≃o B) (k : ℕ) :
    ∃ (m m' : ℕ) (hkm : k ≤ m) (hmm : m ≤ m')
      (f : D (k + 1) → D (m + 1)) (g : D (m + 1) → D (m' + 1)),
      (∀ x, θ (insD k x) = insD m (f x))
        ∧ (∀ y, θ.symm (insD m y) = insD m' (g y))
        ∧ ∀ x, g (f x) = embD (le_trans hkm hmm) x := by
  obtain ⟨m, hkm, f, hdef, -, -, -, -, -⟩ := stage_map_exists θ k
  obtain ⟨m', hmm, g, hgdef, -, -, -, -, -⟩ := stage_map_exists θ.symm m
  refine ⟨m, m', hkm, hmm, f, g, hdef, hgdef, fun x => ?_⟩
  refine insD_injective m' ?_
  rw [insD_embD, ← hgdef (f x), ← hdef x, θ.symm_apply_apply]

-- [D-3329] §3-The-residue-level-local
-- [D-3330] LevelEmbUnique
def LevelEmbUnique : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) → f = embD h

-- [D-3331] levelEmbUnique_diagonal
theorem levelEmbUnique_diagonal (k : ℕ) (f : D (k + 1) → D (k + 1))
    (hmono : Monotone f) (hrefl : ∀ a b, f a ≤ f b → a ≤ b) :
    f = embD (le_refl k) := by
  have hinj : Function.Injective f := fun a b hab =>
    le_antisymm (hrefl a b (le_of_eq hab)) (hrefl b a (le_of_eq hab.symm))
  have hid : f = id := TowerRigidity.D_monotone_injection_eq_id (k + 1) hmono hinj
  funext x
  have hx : f x = x := congrFun hid x
  rw [hx]
  exact (EpPairTower.embLe_self (T := phiTowerEP) (le_refl k) x).symm

-- [D-3332] phiStageDefinable_of_levelEmbUnique
theorem phiStageDefinable_of_levelEmbUnique (h : LevelEmbUnique) :
    PhiRigidity.PhiStageDefinable := by
  intro θ k x
  obtain ⟨m, hkm, f, hdef, hmono, hrefl, hbot, htop, hsup⟩ := stage_map_exists θ k
  refine ⟨x, ?_⟩
  have h1 : θ (insD k x) = insD m (f x) := hdef x
  rw [h k m hkm f hmono hrefl hbot htop hsup] at h1
  exact h1.trans (insD_embD hkm x)

-- [D-3333] B_rigid_of_levelEmbUnique
theorem B_rigid_of_levelEmbUnique (h : LevelEmbUnique) : Subsingleton (B ≃o B) :=
  PhiRigidity.B_rigid_of_stageDefinable (phiStageDefinable_of_levelEmbUnique h)

end StageEmbedding
