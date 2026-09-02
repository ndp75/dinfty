import Dinfty.GlueAAJoin

open GluingTowerLibrary SierpinskiApplication

/-!
# Obstruction (T) does not apply to the F-tower

`Dinfty/TripointedObstruction.lean` proves that a tagwise action of `Φ` must be
**tripointed**, and §79 located the failure precisely: the tower's embedding
`iotaEndP` is not, because `iotaD k ⊤ ≠ ⊤`.  `PhiLimitContinuity` drew the
consequence for ingredient 3 — `δₙ` is not tripointed, so `Φ(δₙ)` is not an
element of the hom-poset.

**All of that is about the constant-embedding tower.**  The F-iterate tower's
embedding is a different map, and it *is* tripointed:

```lean
glueAA_bot (k) : glueAA k ⊥            = ⊥          -- §80
glueAA_mid (k) : glueAA k (dMid (k+1)) = dMid (k+2)
glueAA_top (k) : glueAA k ⊤            = ⊤
```

Contrast `iotaD_ne_top`, which says `iotaD k x ≠ ⊤` for *every* `x`.  So
obstruction (T) is not an obstruction to Theorem A; it is an obstruction to
running the argument on the constant-embedding tower — which is the same thing
the `PsiIso` refutation said, now visible on the functor side.

## Why `glueAA` preserves the marked point

`iotaEndP` acts on a **constant** map by transport:
`iotaEndP k (constHom x) = constHom (iotaD k x)` (`iotaEndPGenM_constHom`).  The
marked point of `EndP (D k)` *is* a constant — `markedPt k = constHom (dMid k)` —
and `dMid (k+1) = iotaD k (dMid k)` by `rfl`.  So the marked points transport
along copy `A` even though a general element does not.

## The payoff: `D∞^F` has all three points

The projections inherit it from the retraction (`qAA_glueAA`), so
`qAA k` is tripointed too, and therefore the three points **assemble along the
F-tower**:

```lean
botF, midF, topF : fTowerReal.Bilim
```

with `BoundedOrder` and `midF` strictly between.  `Φ(D∞^F)` is therefore
*statable*, which it was not before — the constant-embedding tower's `pD` does
not carry `dMid` (it does, in fact: `pD_dMid_succ`; what it does not carry is
`⊤`, since `iotaD` misses it).
-/

open scoped Classical

namespace FTowerTripointed

open GlueAAJoin GlueAAEpPartner

/-! ## The embedding is tripointed -/

/-- Copy `A` transports constants, and the marked point is one. -/
theorem iotaEndP_markedPt (k : ℕ) : iotaEndP k (markedPt k) = markedPt (k + 1) :=
  iotaEndPGenM_constHom (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial (dMid k)

theorem glueAA_mid (k : ℕ) : glueAA k (dMid (k + 1)) = dMid (k + 2) := by
  rw [CopyBCStructure.dMid_eq_glueA k, glueAA_glueA, iotaEndP_markedPt k,
    ← CopyBCStructure.dMid_eq_glueA (k + 1)]

theorem top_eq_glueC (k : ℕ) :
    (⊤ : D (k + 1)) = glueC (markedPt k) (⊤ : EndP (D k))
      (Ne.symm (D_marked_point_nondegenerate k).2.2)
      (Ne.symm (markedPt_ne_top k)) := by
  rw [PhiTriTower.top_succ_eq k]
  exact Subtype.ext rfl

set_option maxHeartbeats 4000000 in
theorem glueAA_top (k : ℕ) : glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) := by
  rw [top_eq_glueC k, glueAA_glueC, top_eq_glueC (k + 1)]
  exact Subtype.ext (congrArg (fun a : EndP (D (k + 1)) => Sum.inr (Sum.inr a))
    (liftT_top k))

/-- **The F-tower's embedding is tripointed** — where the constant-embedding
tower's is not (`iotaD_ne_top`). -/
theorem glueAA_tripointed (k : ℕ) :
    glueAA k (⊥ : D (k + 1)) = ⊥
      ∧ glueAA k (dMid (k + 1)) = dMid (k + 2)
      ∧ glueAA k (⊤ : D (k + 1)) = ⊤ :=
  ⟨GlueAAEpPartner.glueAA_bot k, glueAA_mid k, glueAA_top k⟩

/-- **The contrast, stated.**  `iotaD` misses the top at every argument; that is
obstruction (T)'s one line.  `glueAA` hits it. -/
theorem iotaD_not_top_but_glueAA_is (k : ℕ) :
    (∀ x : D k, iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  ⟨iotaD_ne_top k, glueAA_top k⟩

/-! ## …hence so is the projection -/

theorem qAA_glueAA (k : ℕ) (x : D (k + 1)) : qAA k (glueAA k x) = x :=
  EpFromJoin.upper_map (glueAA k) (glueAAJoinPreserving k)
    (fun _ _ h => glueAA_reflect k h) x

theorem qAA_bot (k : ℕ) : qAA k (⊥ : D (k + 2)) = (⊥ : D (k + 1)) := by
  rw [← GlueAAEpPartner.glueAA_bot k, qAA_glueAA]

theorem qAA_mid (k : ℕ) : qAA k (dMid (k + 2)) = dMid (k + 1) := by
  rw [← glueAA_mid k, qAA_glueAA]

theorem qAA_top (k : ℕ) : qAA k (⊤ : D (k + 2)) = (⊤ : D (k + 1)) := by
  rw [← glueAA_top k, qAA_glueAA]

/-! ## The three points assemble along the F-tower -/

set_option maxHeartbeats 4000000 in
noncomputable def botF : fTowerReal.Bilim :=
  ⟨fun k => (⊥ : D (k + 1)), fun k => qAA_bot k⟩

set_option maxHeartbeats 4000000 in
noncomputable def midF : fTowerReal.Bilim :=
  ⟨fun k => dMid (k + 1), fun k => qAA_mid k⟩

set_option maxHeartbeats 4000000 in
noncomputable def topF : fTowerReal.Bilim :=
  ⟨fun k => (⊤ : D (k + 1)), fun k => qAA_top k⟩

theorem botF_le (y : fTowerReal.Bilim) : botF ≤ y := by
  intro k
  show (⊥ : D (k + 1)) ≤ y.1 k
  exact bot_le

theorem le_topF (y : fTowerReal.Bilim) : y ≤ topF := by
  intro k
  exact @le_top (D (k + 1)) _ _ (y.1 k)

noncomputable instance : OrderBot fTowerReal.Bilim where
  bot := botF
  bot_le := botF_le

noncomputable instance : OrderTop fTowerReal.Bilim where
  top := topF
  le_top := le_topF

noncomputable instance : BoundedOrder fTowerReal.Bilim := {}

theorem midF_ne_botF : midF ≠ botF := by
  intro h
  exact dMid_ne_bot 1 (congrArg (fun z : fTowerReal.Bilim => z.1 0) h)

theorem midF_ne_topF : midF ≠ topF := by
  intro h
  exact dMid_ne_top 1 (congrArg (fun z : fTowerReal.Bilim => z.1 0) h)

/-- **`D∞^F` is a tripointed object.**  Both the bounds and a marked point
strictly between them, all three assembled from the levels — which is possible
exactly because `glueAA` and `qAA` are tripointed. -/
theorem bilim_tripointed :
    (∀ y : fTowerReal.Bilim, botF ≤ y) ∧ (∀ y : fTowerReal.Bilim, y ≤ topF)
      ∧ midF ≠ botF ∧ midF ≠ topF :=
  ⟨botF_le, le_topF, midF_ne_botF, midF_ne_topF⟩

/-! ## But the F-tower is **not** the `Φ`-iterate tower

`Dinfty/EpPairTower.lean`'s header describes the F-tower as
`e'_{k+1} = glueAA k` with the intent that each embedding be `Φ` of the
previous one.  **It is not.**  `glueAA (k+1)`'s copy-`A` action is
`iotaEndP (k+1) = iotaD (k+1) ∘ · ∘ pD (k+1)`, built from the *canonical*
ep-pair one level up; `Φ (glueAA k)`'s would be `glueAA k ∘ · ∘ qAA k`.  Those
differ at `⊤`, and by the same one line as everything else: -/

theorem glueAA_top_ne_iotaD_top (k : ℕ) :
    glueAA k (⊤ : D (k + 1)) ≠ iotaD (k + 1) (⊤ : D (k + 1)) := by
  rw [glueAA_top k]
  exact fun h => iotaD_ne_top (k + 1) (⊤ : D (k + 1)) h.symm

/-- So the two candidate copy-`A` payload maps disagree at `⊤`: the outer map is
`glueAA k` on one side and `iotaD (k+1)` on the other, and `glueAA` hits the top
while `iotaD` never does.  Every `glueAA` in the F-tower is built from the
canonical `(iotaD, pD)` pair at its own level, not from the previous
embedding. -/
theorem fTower_not_phi_iterate (k : ℕ) :
    ∃ w : D (k + 1),
      glueAA k ((⊤ : EndP (D (k + 1))) w) ≠ iotaD (k + 1) ((⊤ : EndP (D (k + 1))) w) :=
  ⟨⊥, glueAA_top_ne_iotaD_top k⟩

end FTowerTripointed
