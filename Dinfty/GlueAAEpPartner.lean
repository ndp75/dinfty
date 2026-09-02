import Dinfty.JoinPrime
import Dinfty.EpFromJoin
import Dinfty.ProjectionTripointed
import Dinfty.TowerShift

open GluingTowerLibrary SierpinskiApplication

/-!
# §79's question, as a single named `Prop` — and what answering it would give

§79 established that `(glueAA k, Φ(p))` is a section/retraction pair but not an
ep-pair (`ProjectionTripointed.not_glueAA_phiP_deflation`), and flagged the next
question: *does `glueAA k` have an ep-partner at all?*  It observed that for an
order-embedding of a finite lattice this is equivalent to preserving joins, and
sketched a reduction to join-primality of two thresholds.

`Dinfty/JoinPrime.lean` discharged the sketch: both thresholds **are**
join-prime, and each of `glueAA`'s two ingredients preserves binary joins.  What
was left was cross-tag bookkeeping, and this module names it:

```lean
GlueAAJoinPreserving k : Prop := ∀ x y : D (k+1), glueAA k (x ⊔ y) = glueAA k x ⊔ glueAA k y
```

and proves everything that hangs off it:

* `exists_glueAA_epPartner` — the ep-partner exists (`Dinfty/EpFromJoin.lean`
  supplies the upper adjoint; `glueAA_bot` and `glueAA_reflect` are the other
  two hypotheses, both discharged here or already on file);
* `fTower` — the **F-iterate tower as an `EpPairTower`**, which is what
  `Dinfty/EpPairTower.lean`'s header asked for and §79 showed `Φ`'s own
  projection cannot supply.

So pillar A's Theorem-A route now rests on one finite, tag-indexed equation per
level, with every consequence of it already drawn.
-/

open scoped Classical

namespace GlueAAEpPartner

open JoinPrimality

/-- **The remaining question of §79**, named. -/
def GlueAAJoinPreserving (k : ℕ) : Prop :=
  ∀ x y : D (k + 1), glueAA k (x ⊔ y) = glueAA k x ⊔ glueAA k y

/-! ## The two hypotheses that are not the question -/

theorem iotaEndP_bot (k : ℕ) :
    iotaEndP k (⊥ : EndP (D k)) = (⊥ : EndP (D (k + 1))) := by
  ext w
  show iotaD k ((⊥ : EndP (D k)) (pD k w)) = (⊥ : EndP (D (k + 1))) w
  rw [endPBot_apply, endPBot_apply]
  exact iotaGenM_bot (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem glueAA_bot (k : ℕ) : glueAA k (⊥ : D (k + 1)) = (⊥ : D (k + 2)) := by
  rw [PhiTriTower.bot_succ_eq k, PhiTriTower.bot_succ_eq (k + 1)]
  exact Subtype.ext (congrArg Sum.inl (iotaEndP_bot k))

/-! ## What the question buys -/

/-- **The ep-partner exists as soon as `glueAA` preserves joins.** -/
theorem exists_glueAA_epPartner (k : ℕ) (h : GlueAAJoinPreserving k) :
    ∃ q : D (k + 2) → D (k + 1), Monotone q ∧ (∀ x, q (glueAA k x) = x)
      ∧ (∀ z, glueAA k (q z) ≤ z) :=
  EpFromJoin.exists_epPartner (glueAA k) (glueAA_bot k) h
    (fun _ _ hab => glueAA_reflect k hab)

/-- The partner, named: the upper adjoint of `glueAA k`. -/
noncomputable def qAA (k : ℕ) : D (k + 2) → D (k + 1) := EpFromJoin.upper (glueAA k)

/-- **The F-iterate tower, as an `EpPairTower`.**  This is the object
`Dinfty/EpPairTower.lean`'s header asked for, and §79 showed `Φ`'s own
projection cannot provide — it exists exactly under `GlueAAJoinPreserving`. -/
noncomputable def fTower (h : ∀ k, GlueAAJoinPreserving k) : EpPairTower where
  carrier k := D (k + 1)
  order k := inferInstance
  emb k := glueAA k
  prj k := qAA k
  emb_mono k := fun _ _ hxy => glueAA_monotone k hxy
  prj_mono k := EpFromJoin.upper_monotone (glueAA k) (glueAA_bot k) (h k)
  retraction k := EpFromJoin.upper_map (glueAA k) (h k) (fun _ _ hab => glueAA_reflect k hab)
  deflation k := EpFromJoin.map_upper_le (glueAA k) (glueAA_bot k) (h k)

@[simp] theorem fTower_carrier (h : ∀ k, GlueAAJoinPreserving k) (k : ℕ) :
    (fTower h).carrier k = D (k + 1) := rfl

@[simp] theorem fTower_emb (h : ∀ k, GlueAAJoinPreserving k) (k : ℕ) :
    (fTower h).emb k = glueAA k := rfl

end GlueAAEpPartner
