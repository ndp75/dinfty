import Dinfty.EmbTagwise
import Dinfty.ColimitCompatPipe

open GluingTowerLibrary SierpinskiApplication

/-!
# `LevelEmbUnique` is FALSE — and obstruction (T) is what refutes it

§114 said the residue could not be proved generically and left it open at the
`D` levels.  This settles the route: **`StageEmbedding.LevelEmbUnique` is false
at the real levels**, so the chain
`LevelImageStableJI → LevelImageStable → LevelEmbUnique → PhiStageDefinable`
cannot close rigidity of `B`.

## The witness

Patch the *legacy* inclusion at the top:

```lean
patched k x = if x = ⊤ then ⊤ else iotaD (k+1) x   :  D (k+1) → D (k+2)
```

Every hypothesis of `LevelEmbUnique` holds, and each one uses a fact the project
already owns:

* **monotone / order-reflecting** — `iotaD_le_iff`, plus **`iotaD_ne_top`** for
  the one cross case (`⊤ ≤ iotaD y` is impossible precisely because `iotaD`
  misses the top);
* **`⊥ ↦ ⊥`** — `iotaD_bot`;
* **`⊤ ↦ ⊤`** — by construction;
* **join-preserving** — `iotaD_sup`, together with **`⊤` being join-irreducible**
  (`top_joinIrred`, from `realUniqueAtomCoatom`: everything below the top is
  below the unique coatom), which is what makes the two-case split total.

And `patched` is *not* `embD`: the tower's embeddings preserve the copy index
(`EmbTagwise.emb_succ_copyIdx`), while `patched` sends every non-top point into
copy `A`.  Evaluating at a copy-`B` point gives `0 = 1`.

## What this means

**Obstruction (T) is the refutation.**  `iotaD_ne_top` — the defect that
disqualified the legacy tower for pillar A and forced the `Φ`-iterate tower — is
exactly the property that makes the patched map order-reflecting.  The same fact
that made the legacy tower useless as a *tower* makes it lethal as a
*competitor*.

This does **not** refute `Subsingleton (B ≃o B)`.  `LevelEmbUnique` was flagged
in §110 as *sufficient, not necessary*: `patched` is a bounded join-embedding
that no automorphism of `B` induces, since `stage_map_comp` requires the stage
maps of `θ` and `θ⁻¹` to compose to `embD`.  So the live route is now the
necessary condition, not the sufficient one — exactly the fallback §113's
stopping rule named.
-/

open scoped Classical

namespace PatchedEmbedding

open PhiIterateTower

/-! ## 1.  `⊤` is join-irreducible at every level -/

theorem top_joinIrred (k : ℕ) {x y : D k} (h : x ⊔ y = (⊤ : D k)) :
    x = ⊤ ∨ y = ⊤ := by
  letI := realUniqueAtomCoatom k
  by_contra hc
  push_neg at hc
  have hx : x ≤ coatomOf (D k) := coatomOf_le hc.1
  have hy : y ≤ coatomOf (D k) := coatomOf_le hc.2
  have : (⊤ : D k) ≤ coatomOf (D k) := h ▸ sup_le hx hy
  exact coatomOf_ne_top (D k) (top_le_iff.mp this)

/-! ## 2.  The patched inclusion -/

noncomputable def patched (k : ℕ) (x : D (k + 1)) : D (k + 2) :=
  if x = ⊤ then ⊤ else iotaD (k + 1) x

theorem patched_of_ne_top {k : ℕ} {x : D (k + 1)} (hx : x ≠ ⊤) :
    patched k x = iotaD (k + 1) x := if_neg hx

@[simp] theorem patched_top (k : ℕ) : patched k (⊤ : D (k + 1)) = ⊤ := if_pos rfl

theorem patched_bot (k : ℕ) : patched k (⊥ : D (k + 1)) = (⊥ : D (k + 2)) := by
  have hbt : (⊥ : D (k + 1)) ≠ (⊤ : D (k + 1)) := bot_ne_top_of_nontrivial
  rw [patched_of_ne_top hbt]
  exact ColimitCompatPipe.iotaD_bot (k + 1)

theorem patched_monotone (k : ℕ) : Monotone (patched k) := by
  intro x y hxy
  by_cases hy : y = ⊤
  · rw [hy, patched_top]; exact le_top
  · have hx : x ≠ ⊤ := fun hc => hy (top_le_iff.mp (hc ▸ hxy))
    rw [patched_of_ne_top hx, patched_of_ne_top hy]
    exact iotaD_monotone (k + 1) hxy

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

/-! ## 3.  It is not the canonical embedding -/

theorem patched_val_ne_top {k : ℕ} {x : D (k + 1)} (hx : x ≠ ⊤) :
    ∃ a : EndP (D (k + 1)), (patched k x).1 = Sum.inl a := by
  rw [patched_of_ne_top hx]
  exact ⟨constHom x, rfl⟩

/-! ## 4.  The refutation

A copy-`B` point of `D 2` that is not the top.  `patched 1` sends it into copy
`A`; `embD` keeps it in copy `B` (`EmbTagwise.emb_succ_copyIdx`).  So the two
maps differ, and `LevelEmbUnique` is false. -/

open CopyHierarchy

private theorem hmt1 : (markedPt 1) ≠ ⊤ := (D_marked_point_nondegenerate 1).2.1
private theorem hbt1 : (⊥ : EndP (D 1)) ≠ ⊤ := (D_marked_point_nondegenerate 1).2.2

theorem top_val_two : (⊤ : D 2).1 = Sum.inr (Sum.inr (⊤ : EndP (D 1))) := by
  show canonGen (markedPt 1) (Sum.inr (Sum.inr (⊤ : EndP (D 1)))) = _
  rw [canonGen, if_neg (Ne.symm hbt1), if_neg (Ne.symm hmt1)]

/-- A copy-`B` point of `D 2`. -/
noncomputable def wB : D 2 := glueB (markedPt 1) (⊤ : EndP (D 1)) (Ne.symm hbt1)

theorem wB_val : wB.1 = Sum.inr (Sum.inl (⊤ : EndP (D 1))) := rfl

theorem wB_ne_top : wB ≠ (⊤ : D 2) := by
  intro h
  have hv := congrArg Subtype.val h
  rw [wB_val, top_val_two] at hv
  exact Sum.inl_ne_inr (Sum.inr_injective hv)

theorem copyIdx_wB : copyIdx wB.1 = 1 := by rw [wB_val]; rfl

/-- **`LevelEmbUnique` is false.** -/
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

/-- …and therefore so is every statement above it in the chain. -/
theorem not_levelImageStable : ¬ EmbDImage.LevelImageStable := fun h =>
  not_levelEmbUnique (EmbDImage.levelEmbUnique_of_levelImageStable h)

/-- **The whole residue chain of sections 110-111 is refuted.** -/
theorem not_levelImageStableJI : ¬ EmbDImage.LevelImageStableJI := fun h =>
  not_levelImageStable (EmbDImage.levelImageStable_of_JI h)

end PatchedEmbedding
