import Dinfty.PhiStagePipe

open GluingTowerLibrary SierpinskiApplication

/-!
# What an automorphism of `B` looks like on a stage

§109 left `PhiStageDefinable` as the one open link, and said the seed comparison
would have to be redone against `Set.range (emb n)`.  This module takes that
seriously and finds that **no seed comparison is needed**: the residue is a
statement about maps between two finite levels, with no `DInfty`, no bilimit and
no join-irreducibility in it.

## The unconditional theorem

Stage `k` is finite, so an automorphism `θ` sends it inside a single later stage
`m` (`stages_union_preserved` plus a `Finset.sup`).  Reading that off level `m`
gives a map `f : D (k+1) → D (m+1)`, and every property it has is forced:

```lean
stage_map_exists (θ) (k) :
  ∃ m, k ≤ m ∧ ∃ f : D (k+1) → D (m+1),
    (∀ x, θ (insD k x) = insD m (f x))
      ∧ Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b)
      ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧ (∀ a b, f (a ⊔ b) = f a ⊔ f b)
```

* order-reflecting, from `θ.symm`;
* `⊥`/`⊤`-preserving, because `insD k ⊥ = ⊥` and `insD k ⊤ = ⊤` for *every* `k`
  — that is the tower's tripointedness, and it is exactly what the legacy tower
  does not have;
* join-preserving, because `insD k` is a **left adjoint** (`ins_le_iff'`), so
  `IsLUB {insD k a, insD k b} (insD k (a ⊔ b))`, and an order isomorphism
  carries least upper bounds to least upper bounds.

`embLe` is one such map.  So the whole question is whether it is the only one.

## The residue, level-local

```lean
def LevelEmbUnique : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k+1) → D (m+1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
    (∀ a b, f (a ⊔ b) = f a ⊔ f b) → f = phiTowerEP.embLe h
```

`phiStageDefinable_of_levelEmbUnique` closes the chain from it, so

```
LevelEmbUnique → PhiStageDefinable → Subsingleton (B ≃o B)
```

**REFUTED (see `Dinfty/PatchedEmbedding.lean`).**  `LevelEmbUnique` is *false*
at the real levels: `patched k x = if x = ⊤ then ⊤ else iotaD (k+1) x` satisfies
every hypothesis and is not `embD`.  Caveat 1 below is what actually happened —
the condition was sufficient, not necessary, and it is the sufficiency that
failed.  Everything else in this module stands; only the `LevelEmbUnique` route
is dead.

Two honest caveats.

1. **Sufficient, not necessary.**  Not every such `f` need come from a `θ`, so
   `LevelEmbUnique` could fail while `PhiStageDefinable` still holds.  It is the
   *intended route*, in the same sense `NoCrossFiberTie` was pillar B's.
2. **The `k = m` case is already a theorem** — `D_monotone_injection_eq_id`, and
   `embLe (le_refl k)` is the identity — so `LevelEmbUnique` is a genuine
   generalisation of a fact the project already owns, not a new species.

## Why this is not the refuted "cross-level embedding rigidity"

Handoff §7-era work refuted cross-level rigidity for **monotone injections**:
there are 1248 three-chains in the real `D_1` against one canonical, so a
monotone injection `D k → D N` need not be `iotaLe`.  Every one of the three
extra conditions here is doing work against that: a three-chain witness
`D 0 → D 1` must now also fix `⊥` and `⊤` and preserve joins, and — decisively —
the `Φ`-tower's levels start at `D 1`, so the domain is never a chain.  The
counterexample family does not survive the strengthening; whether *some* family
does is exactly the open question.
-/

open Set

open scoped Classical

namespace StageEmbedding

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe

/-! ## 1.  The stage is a bounded sub-join-semilattice -/

theorem insD_le_insD_iff (k : ℕ) (a b : D (k + 1)) : insD k a ≤ insD k b ↔ a ≤ b :=
  StageRigidity.ins_le_iff (T := phiTowerEP) k a b

theorem insD_injective (k : ℕ) : Function.Injective (insD k) :=
  StageRigidity.ins_injective (T := phiTowerEP) k

theorem insD_bot (k : ℕ) : insD k (⊥ : D (k + 1)) = (⊥ : B) := PhiBilimit.ins_bot k

theorem insD_top (k : ℕ) : insD k (⊤ : D (k + 1)) = (⊤ : B) := PhiBilimit.ins_top k

/-- The canonical level-to-level map, with its domain and codomain spelled as
levels so that `⊔` and friends resolve. -/
noncomputable def embD {k m : ℕ} (h : k ≤ m) (a : D (k + 1)) : D (m + 1) :=
  phiTowerEP.embLe h a

theorem insD_embD {k m : ℕ} (h : k ≤ m) (a : D (k + 1)) : insD m (embD h a) = insD k a :=
  EpPairTower.ins_embLe (T := phiTowerEP) h a

/-- **`insD k` preserves binary joins** — because it is a left adjoint. -/
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

/-- The tower's embeddings preserve binary joins, at every level.  Free from the
adjunction: `insD` preserves them and is injective. -/
theorem embD_sup {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    embD h (a ⊔ b) = embD h a ⊔ embD h b := by
  refine insD_injective m ?_
  have hL := insD_isLUB_pair m (embD h a) (embD h b)
  rw [insD_embD h a, insD_embD h b] at hL
  rw [insD_embD h (a ⊔ b)]
  exact (insD_isLUB_pair k a b).unique hL

/-! ## 2.  The stage map of an automorphism -/

/-- **The unconditional shape theorem.**  On each stage an automorphism of `B`
is a bounded join-embedding of one level into a later one. -/
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
  · -- monotone
    intro a b hab
    refine (insD_le_insD_iff m _ _).mp ?_
    rw [← hdef a, ← hdef b]
    exact θ.monotone ((insD_le_insD_iff k a b).mpr hab)
  · -- order-reflecting
    intro a b hab
    have h1 : θ (insD k a) ≤ θ (insD k b) := by
      rw [hdef a, hdef b]
      exact insD_monotone m hab
    exact (insD_le_insD_iff k a b).mp (θ.le_iff_le.mp h1)
  · -- bottom
    refine insD_injective m ?_
    rw [← hdef ⊥, insD_bot k, insD_bot m]
    exact θ.map_bot
  · -- top
    refine insD_injective m ?_
    rw [← hdef ⊤, insD_top k, insD_top m]
    exact θ.map_top
  · -- joins
    intro a b
    refine insD_injective m ?_
    have himg : IsLUB (θ '' {insD k a, insD k b}) (θ (insD k (a ⊔ b))) :=
      (OrderIso.isLUB_image' θ).mpr (insD_isLUB_pair k a b)
    rw [Set.image_pair, hdef a, hdef b, hdef (a ⊔ b)] at himg
    exact himg.unique (insD_isLUB_pair m _ _)

/-- **The stage maps of `θ` and `θ⁻¹` compose to the canonical inclusion.**  So a
counterexample to `LevelEmbUnique` that actually came from an automorphism would
have to *split* like this — which is why `LevelEmbUnique` is stronger than the
chain strictly needs. -/
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

/-! ## 3.  The residue, level-local -/

/-- **The residue.**  A bounded join-embedding of one level into a later one is
the canonical one.  Finite, level-local: no bilimit, no seeds, no
join-irreducibility. -/
def LevelEmbUnique : Prop :=
  ∀ (k m : ℕ) (h : k ≤ m) (f : D (k + 1) → D (m + 1)),
    Monotone f → (∀ a b, f a ≤ f b → a ≤ b) → f ⊥ = ⊥ → f ⊤ = ⊤ →
      (∀ a b, f (a ⊔ b) = f a ⊔ f b) → f = embD h

/-- The case `k = m` is already a theorem: `D_monotone_injection_eq_id`. -/
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

/-- **The chain closes from it.** -/
theorem phiStageDefinable_of_levelEmbUnique (h : LevelEmbUnique) :
    PhiRigidity.PhiStageDefinable := by
  intro θ k x
  obtain ⟨m, hkm, f, hdef, hmono, hrefl, hbot, htop, hsup⟩ := stage_map_exists θ k
  refine ⟨x, ?_⟩
  have h1 : θ (insD k x) = insD m (f x) := hdef x
  rw [h k m hkm f hmono hrefl hbot htop hsup] at h1
  exact h1.trans (insD_embD hkm x)

theorem B_rigid_of_levelEmbUnique (h : LevelEmbUnique) : Subsingleton (B ≃o B) :=
  PhiRigidity.B_rigid_of_stageDefinable (phiStageDefinable_of_levelEmbUnique h)

end StageEmbedding
