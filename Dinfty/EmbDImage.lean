import Dinfty.StageEmbedding

open GluingTowerLibrary SierpinskiApplication

/-!
# `embD`, formalized: the residue is only about the **image**

§110 reduced rigidity of `B` to `LevelEmbUnique` — *a bounded join-embedding of
one level into a later one is the canonical one*.  This module formalizes `embD`
properly and shows that the conclusion `f = embD h` is **not** where the content
is: it follows from `D_monotone_injection_eq_id` the moment `f`'s values land in
the image of `embD`.

## `embD` has a retraction

`embD h` is one half of an ep-pair; `prjD h := phiTowerEP.prjLe h` is the other:

```lean
prjD_embD (h) (x) : prjD h (embD h x) = x
embD_prjD_le (h) (z) : embD h (prjD h z) ≤ z
```

so `embD h ∘ prjD h` is a deflation idempotent and

```lean
mem_range_embD_iff (h) (z) : z ∈ Set.range (embD h) ↔ embD h (prjD h z) = z
```

The image is therefore an order-theoretically named subset of the *finite* level
`D (m+1)`, not a black box.

## Measuring the image

Both `embD h` and any order-reflecting `f` are injective, so both images have
exactly `Nat.card (D (k+1))` elements (`ncard_range_embD`,
`ncard_range_of_reflecting`).  In a finite level, same size plus containment
gives equality (`range_eq_of_subset`) — so "lands in the image" and "has the same
image" are interchangeable.

## The reduction

```lean
eq_embD_of_range_subset (h) (f) : Monotone f → order-reflecting →
    (∀ x, f x ∈ Set.range (embD h)) → f = embD h
```

Proof: `g := prjD h ∘ f` is a monotone injection `D (k+1) → D (k+1)`, hence the
identity (`D_monotone_injection_eq_id`), and `f x = embD h (g x) = embD h x`.
**Neither the bounds nor the joins are used.**  They are hypotheses that can only
earn their keep by constraining where `f` sends things.

So the residue becomes

```lean
def LevelImageStable : Prop := ∀ k m (h : k ≤ m) (f : D (k+1) → D (m+1)),
  Monotone f → order-reflecting → f ⊥ = ⊥ → f ⊤ = ⊤ → join-preserving →
    ∀ x, embD h (prjD h (f x)) = f x
```

`LevelImageStable → LevelEmbUnique → PhiStageDefinable → Subsingleton (B ≃o B)`.

And `embD` itself satisfies every hypothesis (`embD_bot`, `embD_top`,
`embD_sup`, `embD_le_iff`), so the statement is not vacuous: it says the
canonical map is alone in its class.

## …and only at join-irreducibles

`f ⊥ = ⊥` and join-preservation finally earn their keep in
`image_stable_of_joinIrred`: they make `f` commute with `Finset.sup`, and
`Set.range (embD h)` is closed under joins and contains `⊥`, so the image
condition need only be checked where `f` is not determined —

```lean
LevelImageStableJI : … → ∀ y, JoinIrred (D (k+1)) y → f y ∈ Set.range (embD h)
```

`B_rigid_of_levelImageStableJI` closes the chain from that.  So the final
residue is a statement about **join-irreducibles of one finite level and the
image of one canonical map** — the same objects pillar B's `FirstSlice` was
about, now on the image side rather than the seed side.
-/

open Set

open scoped Classical

namespace EmbDImage

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding

/-! ## 1.  The staged ep-pair, abstractly -/

variable {T : EpPairTower}

/-- `prjLe` retracts `embLe`, at any gap. -/
theorem prjLe_embLe {k n : ℕ} (h : k ≤ n) (x : T.carrier k) :
    T.prjLe h (T.embLe h x) = x := by
  induction n, h using Nat.le_induction with
  | base => rw [EpPairTower.embLe_self, EpPairTower.prjLe_self]
  | succ n hkn ih =>
      rw [EpPairTower.prjLe_succ hkn (Nat.le_succ_of_le hkn),
        EpPairTower.prj_embLe hkn (Nat.le_succ_of_le hkn), ih]

/-- …and `embLe ∘ prjLe` is a deflation at any gap. -/
theorem embLe_prjLe_le {k n : ℕ} (h : k ≤ n) (z : T.carrier n) :
    T.embLe h (T.prjLe h z) ≤ z := by
  induction n, h using Nat.le_induction with
  | base => rw [EpPairTower.prjLe_self, EpPairTower.embLe_self]
  | succ n hkn ih =>
      rw [EpPairTower.prjLe_succ hkn (Nat.le_succ_of_le hkn),
        EpPairTower.embLe_succ hkn (Nat.le_succ_of_le hkn)]
      exact le_trans (T.emb_mono n (ih (T.prj n z))) (T.deflation n z)

/-! ## 2.  `prjD`, and the image of `embD` -/

/-- The level-to-level projection, with its types spelled as levels. -/
noncomputable def prjD {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) : D (k + 1) :=
  phiTowerEP.prjLe h z

theorem prjD_embD {k m : ℕ} (h : k ≤ m) (x : D (k + 1)) : prjD h (embD h x) = x :=
  prjLe_embLe (T := phiTowerEP) h x

theorem embD_prjD_le {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) : embD h (prjD h z) ≤ z :=
  embLe_prjLe_le (T := phiTowerEP) h z

theorem prjD_monotone {k m : ℕ} (h : k ≤ m) : Monotone (prjD h) :=
  fun _ _ hab => EpPairTower.prjLe_mono (T := phiTowerEP) h hab

theorem embD_le_iff {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    embD h a ≤ embD h b ↔ a ≤ b :=
  EpPairTower.embLe_le_iff (T := phiTowerEP) h a b

theorem embD_monotone {k m : ℕ} (h : k ≤ m) : Monotone (embD h) :=
  fun _ _ hab => (embD_le_iff h _ _).mpr hab

theorem embD_injective {k m : ℕ} (h : k ≤ m) : Function.Injective (embD h) :=
  fun _ _ hab => (embD_le_iff h _ _).mp hab.le |>.antisymm ((embD_le_iff h _ _).mp hab.ge)

/-- **The image of `embD`, named**: it is the fixed-point set of the deflation
idempotent `embD ∘ prjD`. -/
theorem mem_range_embD_iff {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    z ∈ Set.range (embD h) ↔ embD h (prjD h z) = z := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [prjD_embD]
  · exact fun hz => ⟨prjD h z, hz⟩

/-! ## 3.  `embD` satisfies every hypothesis of the residue

So `LevelEmbUnique` is a statement about a nonempty class: the canonical map is
in it, and the question is whether anything else is. -/

theorem embD_bot {k m : ℕ} (h : k ≤ m) : embD h (⊥ : D (k + 1)) = (⊥ : D (m + 1)) := by
  refine insD_injective m ?_
  rw [insD_embD h (⊥ : D (k + 1)), insD_bot k, insD_bot m]

theorem embD_top {k m : ℕ} (h : k ≤ m) : embD h (⊤ : D (k + 1)) = (⊤ : D (m + 1)) := by
  refine insD_injective m ?_
  rw [insD_embD h (⊤ : D (k + 1)), insD_top k, insD_top m]

/-! ## 4.  Measuring the image -/

theorem ncard_range_embD {k m : ℕ} (h : k ≤ m) :
    (Set.range (embD h)).ncard = Nat.card (D (k + 1)) := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ (embD_injective h), Set.ncard_univ]

theorem ncard_range_of_reflecting {k m : ℕ} (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) :
    (Set.range f).ncard = Nat.card (D (k + 1)) := by
  have hinj : Function.Injective f := fun a b hab =>
    le_antisymm (hrefl a b (le_of_eq hab)) (hrefl b a (le_of_eq hab.symm))
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]

/-- **The finite case measures the image.**  Containment upgrades to equality,
because both sides have exactly `Nat.card (D (k+1))` elements in a finite
level. -/
theorem range_eq_of_subset {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hsub : Set.range f ⊆ Set.range (embD h)) :
    Set.range f = Set.range (embD h) := by
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [ncard_range_embD h, ncard_range_of_reflecting f hrefl]

/-! ## 5.  The reduction: only the image matters -/

/-- **`f = embD h` follows from where `f` sends things.**  Neither the bounds nor
the joins are used here — they can only earn their keep upstream, by pinning the
image. -/
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

/-! ## 6.  The residue, restated as an image statement -/

/-- **The residue.**  A bounded join-embedding of one level into a later one
takes its values in the image of the canonical map. -/
def LevelImageStable : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) → ∀ x, embD h (prjD h (f x)) = f x

theorem levelEmbUnique_of_levelImageStable (h : LevelImageStable) : LevelEmbUnique :=
  fun k m hkm f hmono hrefl hbot htop hsup =>
    eq_embD_of_range_subset hkm f hmono hrefl (h k m hkm f hmono hrefl hbot htop hsup)

theorem B_rigid_of_levelImageStable (h : LevelImageStable) : Subsingleton (B ≃o B) :=
  B_rigid_of_levelEmbUnique (levelEmbUnique_of_levelImageStable h)

/-! ## 7.  And only at join-irreducibles

Here is where `f ⊥ = ⊥` and join-preservation finally earn their keep: they make
`f` determined by its values on join-irreducibles, and `Set.range (embD h)` is
closed under joins and contains `⊥`.  So the residue need only be checked at the
join-irreducibles of `D (k+1)` — the same objects pillar B's `FirstSlice` was
about, now on the image side. -/

theorem range_embD_sup_closed {k m : ℕ} (h : k ≤ m) {u v : D (m + 1)}
    (hu : u ∈ Set.range (embD h)) (hv : v ∈ Set.range (embD h)) :
    u ⊔ v ∈ Set.range (embD h) := by
  obtain ⟨p, rfl⟩ := hu
  obtain ⟨q, rfl⟩ := hv
  exact ⟨p ⊔ q, embD_sup h p q⟩

theorem range_embD_bot_mem {k m : ℕ} (h : k ≤ m) :
    (⊥ : D (m + 1)) ∈ Set.range (embD h) := ⟨⊥, embD_bot h⟩

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

/-- A `⊥`-preserving, join-preserving map commutes with `Finset.sup`. -/
theorem map_finset_sup {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (S : Finset (D (k + 1))) :
    f (S.sup id) = S.sup f := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sup_empty]; exact hbot
  | @insert a S _ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih, ← hsup]
      rfl

/-- **The residue only has to be checked at join-irreducibles.** -/
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

/-- …so this suffices, and it mentions only join-irreducibles. -/
def LevelImageStableJI : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) →
        ∀ y : D (k + 1), JoinIrred (D (k + 1)) y → f y ∈ Set.range (embD h)

theorem levelImageStable_of_JI (h : LevelImageStableJI) : LevelImageStable :=
  fun k m hkm f hmono hrefl hbot htop hsup =>
    image_stable_of_joinIrred hkm f hbot hsup (h k m hkm f hmono hrefl hbot htop hsup)

theorem B_rigid_of_levelImageStableJI (h : LevelImageStableJI) : Subsingleton (B ≃o B) :=
  B_rigid_of_levelImageStable (levelImageStable_of_JI h)

/-! ## 8.  The chain, in one place — and it is refuted

Everything above is a waypoint.  `LevelImageStableJI` was posted as the only
statement left between the library and rigidity of Theorem A's carrier.  **It is
false** (`PatchedEmbedding.not_levelImageStableJI`), so this chain does not close
rigidity; its implications remain correct and reusable. -/

/-- **The chain, in one theorem.**  Every implication here is proved.

**But the antecedent is FALSE** — `PatchedEmbedding.not_levelImageStableJI`.
This was posted as "the finish line"; it was not.  `LevelImageStableJI` implies
`LevelEmbUnique`, and `LevelEmbUnique` is refuted by patching `iotaD` at the top.
The chain is kept because the implications are correct and reusable; what is
dead is using it to close rigidity of `B`.  The live route is the *necessary*
condition, `StageEmbedding.stage_map_comp`. -/
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

/-- The diagonal case, again free: at `k = m` the image is everything. -/
theorem levelImageStable_diagonal (k : ℕ) (z : D (k + 1)) :
    embD (le_refl k) (prjD (le_refl k) z) = z := by
  change phiTowerEP.embLe (le_refl k) (phiTowerEP.prjLe (le_refl k) z) = z
  rw [EpPairTower.prjLe_self, EpPairTower.embLe_self]

end EmbDImage
