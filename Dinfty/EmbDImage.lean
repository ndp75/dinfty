import Dinfty.StageEmbedding

open GluingTowerLibrary SierpinskiApplication

-- [D-3334] §embD-formalized-the-residue-is-only-about
open Set

open scoped Classical

namespace EmbDImage

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding

-- [D-3335] §1-The-staged-ep-pair-abstractly
variable {T : EpPairTower}

-- [D-3336] prjLe_embLe
theorem prjLe_embLe {k n : ℕ} (h : k ≤ n) (x : T.carrier k) :
    T.prjLe h (T.embLe h x) = x := by
  induction n, h using Nat.le_induction with
  | base => rw [EpPairTower.embLe_self, EpPairTower.prjLe_self]
  | succ n hkn ih =>
      rw [EpPairTower.prjLe_succ hkn (Nat.le_succ_of_le hkn),
        EpPairTower.prj_embLe hkn (Nat.le_succ_of_le hkn), ih]

-- [D-3337] embLe_prjLe_le
theorem embLe_prjLe_le {k n : ℕ} (h : k ≤ n) (z : T.carrier n) :
    T.embLe h (T.prjLe h z) ≤ z := by
  induction n, h using Nat.le_induction with
  | base => rw [EpPairTower.prjLe_self, EpPairTower.embLe_self]
  | succ n hkn ih =>
      rw [EpPairTower.prjLe_succ hkn (Nat.le_succ_of_le hkn),
        EpPairTower.embLe_succ hkn (Nat.le_succ_of_le hkn)]
      exact le_trans (T.emb_mono n (ih (T.prj n z))) (T.deflation n z)

-- [D-3338] §2-prjD-and-the-image-of-embD
-- [D-3339] prjD
noncomputable def prjD {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) : D (k + 1) :=
  phiTowerEP.prjLe h z

-- [D-3340] prjD_embD
theorem prjD_embD {k m : ℕ} (h : k ≤ m) (x : D (k + 1)) : prjD h (embD h x) = x :=
  prjLe_embLe (T := phiTowerEP) h x

-- [D-3341] embD_prjD_le
theorem embD_prjD_le {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) : embD h (prjD h z) ≤ z :=
  embLe_prjLe_le (T := phiTowerEP) h z

-- [D-3342] prjD_monotone
theorem prjD_monotone {k m : ℕ} (h : k ≤ m) : Monotone (prjD h) :=
  fun _ _ hab => EpPairTower.prjLe_mono (T := phiTowerEP) h hab

-- [D-3343] embD_le_iff
theorem embD_le_iff {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    embD h a ≤ embD h b ↔ a ≤ b :=
  EpPairTower.embLe_le_iff (T := phiTowerEP) h a b

-- [D-3344] embD_monotone
theorem embD_monotone {k m : ℕ} (h : k ≤ m) : Monotone (embD h) :=
  fun _ _ hab => (embD_le_iff h _ _).mpr hab

-- [D-3345] embD_injective
theorem embD_injective {k m : ℕ} (h : k ≤ m) : Function.Injective (embD h) :=
  fun _ _ hab => (embD_le_iff h _ _).mp hab.le |>.antisymm ((embD_le_iff h _ _).mp hab.ge)

-- [D-3346] mem_range_embD_iff
theorem mem_range_embD_iff {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    z ∈ Set.range (embD h) ↔ embD h (prjD h z) = z := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [prjD_embD]
  · exact fun hz => ⟨prjD h z, hz⟩

-- [D-3347] §3-embD-satisfies-every-hypothesis-of-the-residue
-- [D-3348] embD_bot
theorem embD_bot {k m : ℕ} (h : k ≤ m) : embD h (⊥ : D (k + 1)) = (⊥ : D (m + 1)) := by
  refine insD_injective m ?_
  rw [insD_embD h (⊥ : D (k + 1)), insD_bot k, insD_bot m]

-- [D-3349] embD_top
theorem embD_top {k m : ℕ} (h : k ≤ m) : embD h (⊤ : D (k + 1)) = (⊤ : D (m + 1)) := by
  refine insD_injective m ?_
  rw [insD_embD h (⊤ : D (k + 1)), insD_top k, insD_top m]

-- [D-3350] §4-Measuring-the-image
-- [D-3351] ncard_range_embD
theorem ncard_range_embD {k m : ℕ} (h : k ≤ m) :
    (Set.range (embD h)).ncard = Nat.card (D (k + 1)) := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ (embD_injective h), Set.ncard_univ]

-- [D-3352] ncard_range_of_reflecting
theorem ncard_range_of_reflecting {k m : ℕ} (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) :
    (Set.range f).ncard = Nat.card (D (k + 1)) := by
  have hinj : Function.Injective f := fun a b hab =>
    le_antisymm (hrefl a b (le_of_eq hab)) (hrefl b a (le_of_eq hab.symm))
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]

-- [D-3353] range_eq_of_subset
theorem range_eq_of_subset {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hsub : Set.range f ⊆ Set.range (embD h)) :
    Set.range f = Set.range (embD h) := by
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [ncard_range_embD h, ncard_range_of_reflecting f hrefl]

-- [D-3354] §5-The-reduction-only-the-image-matters
-- [D-3355] eq_embD_of_range_subset
theorem eq_embD_of_range_subset {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hmono : Monotone f) (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hrange : ∀ x, embD h (prjD h (f x)) = f x) : f = embD h := by
  have hinj : Function.Injective f := fun a b hab =>
    le_antisymm (hrefl a b (le_of_eq hab)) (hrefl b a (le_of_eq hab.symm))
  have hgmono : Monotone (fun x => prjD h (f x)) := fun a b hab =>
    (embD_le_iff h _ _).mp (by rw [hrange a, hrange b]; exact hmono hab)
  have hginj : Function.Injective (fun x => prjD h (f x)) := by
    intro a b hab
    refine hinj ?_
    rw [← hrange a, ← hrange b]
    exact congrArg (embD h) hab
  have hid : (fun x => prjD h (f x)) = id :=
    TowerRigidity.D_monotone_injection_eq_id (k + 1) hgmono hginj
  funext x
  rw [← hrange x, show prjD h (f x) = x from congrFun hid x]

-- [D-3356] §6-The-residue-restated-as-an-image-statement
-- [D-3357] LevelImageStable
def LevelImageStable : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) → ∀ x, embD h (prjD h (f x)) = f x

-- [D-3358] levelEmbUnique_of_levelImageStable
theorem levelEmbUnique_of_levelImageStable (h : LevelImageStable) : LevelEmbUnique :=
  fun k m hkm f hmono hrefl hbot htop hsup =>
    eq_embD_of_range_subset hkm f hmono hrefl (h k m hkm f hmono hrefl hbot htop hsup)

-- [D-3359] B_rigid_of_levelImageStable
theorem B_rigid_of_levelImageStable (h : LevelImageStable) : Subsingleton (B ≃o B) :=
  B_rigid_of_levelEmbUnique (levelEmbUnique_of_levelImageStable h)

-- [D-3360] §7-And-only-at-join-irreducibles
-- [D-3361] range_embD_sup_closed
theorem range_embD_sup_closed {k m : ℕ} (h : k ≤ m) {u v : D (m + 1)}
    (hu : u ∈ Set.range (embD h)) (hv : v ∈ Set.range (embD h)) :
    u ⊔ v ∈ Set.range (embD h) := by
  obtain ⟨p, rfl⟩ := hu
  obtain ⟨q, rfl⟩ := hv
  exact ⟨p ⊔ q, embD_sup h p q⟩

-- [D-3362] range_embD_bot_mem
theorem range_embD_bot_mem {k m : ℕ} (h : k ≤ m) :
    (⊥ : D (m + 1)) ∈ Set.range (embD h) := ⟨⊥, embD_bot h⟩

-- [D-3363] finset_sup_mem_range
theorem finset_sup_mem_range {k m : ℕ} (h : k ≤ m) (g : D (k + 1) → D (m + 1))
    (S : Finset (D (k + 1))) (hg : ∀ y ∈ S, g y ∈ Set.range (embD h)) :
    S.sup g ∈ Set.range (embD h) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact range_embD_bot_mem h
  | @insert a S _ha ih =>
      rw [Finset.sup_insert]
      exact range_embD_sup_closed h (hg a (Finset.mem_insert_self a S))
        (ih (fun y hy => hg y (Finset.mem_insert_of_mem hy)))

-- [D-3364] map_finset_sup
theorem map_finset_sup {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (S : Finset (D (k + 1))) :
    f (S.sup id) = S.sup f := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sup_empty]; exact hbot
  | @insert a S _ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih, ← hsup]
      rfl

-- [D-3365] image_stable_of_joinIrred
theorem image_stable_of_joinIrred {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hbot : f ⊥ = ⊥) (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (hji : ∀ y : D (k + 1), JoinIrred (D (k + 1)) y → f y ∈ Set.range (embD h)) :
    ∀ x, embD h (prjD h (f x)) = f x := by
  classical
  intro x
  refine (mem_range_embD_iff h (f x)).mp ?_
  have hx : x = (Finset.univ.filter (fun q : D (k + 1) =>
      JoinIrred (D (k + 1)) q ∧ q ≤ x)).sup id := finite_lattice_eq_sup_joinIrreds x
  rw [hx, map_finset_sup f hbot hsup]
  refine finset_sup_mem_range h f _ (fun y hy => ?_)
  exact hji y (Finset.mem_filter.mp hy).2.1

-- [D-3366] LevelImageStableJI
def LevelImageStableJI : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) →
        ∀ y : D (k + 1), JoinIrred (D (k + 1)) y → f y ∈ Set.range (embD h)

-- [D-3367] levelImageStable_of_JI
theorem levelImageStable_of_JI (h : LevelImageStableJI) : LevelImageStable :=
  fun k m hkm f hmono hrefl hbot htop hsup =>
    image_stable_of_joinIrred hkm f hbot hsup (h k m hkm f hmono hrefl hbot htop hsup)

-- [D-3368] B_rigid_of_levelImageStableJI
theorem B_rigid_of_levelImageStableJI (h : LevelImageStableJI) : Subsingleton (B ≃o B) :=
  B_rigid_of_levelImageStable (levelImageStable_of_JI h)

-- [D-3369] §8-The-chain-in-one-place-and-it-is-refuted
-- [D-3370] rigidity_finish_line
theorem rigidity_finish_line :
    (LevelImageStableJI → Subsingleton (B ≃o B))
      ∧ (LevelImageStableJI → LevelImageStable)
      ∧ (LevelImageStable → LevelEmbUnique)
      ∧ (LevelEmbUnique → PhiRigidity.PhiStageDefinable)
      ∧ (PhiRigidity.PhiStageDefinable → Subsingleton (B ≃o B)) :=
  ⟨B_rigid_of_levelImageStableJI, levelImageStable_of_JI,
    levelEmbUnique_of_levelImageStable,
    StageEmbedding.phiStageDefinable_of_levelEmbUnique,
    PhiRigidity.B_rigid_of_stageDefinable⟩

-- [D-3371] levelImageStable_diagonal
theorem levelImageStable_diagonal (k : ℕ) (z : D (k + 1)) :
    embD (le_refl k) (prjD (le_refl k) z) = z := by
  change phiTowerEP.embLe (le_refl k) (phiTowerEP.prjLe (le_refl k) z) = z
  rw [EpPairTower.prjLe_self, EpPairTower.embLe_self]

end EmbDImage
