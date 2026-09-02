import Dinfty.FTowerTripointed

open GluingTowerLibrary SierpinskiApplication

/-!
# The genuine `Φ`-iterate tower

§83 showed the F-tower is *not* the `Φ`-iterate tower: its embeddings are all
built from the canonical `(iotaD, pD)` pair at their own level, not from the
previous embedding.  The standard bilimit argument needs the shifted tower to
**be** `Φ` of the tower, so it needs a tower where that holds by construction.

This module builds one.

## The step, and why it is pure functoriality

A tripointed ep-pair `(e, p) : D k ⇄ D (k+1)` induces two tripointed morphisms
of glue bases,

```lean
endUp   E : TowerHom k (k+1)     -- h ↦ e ∘ h ∘ p
endDown E : TowerHom (k+1) k     -- h ↦ p ∘ h ∘ e
```

— tripointed because `e` and `p` preserve `⊥`, the marked point and `⊤`, and
because the marked point of `EndP (D k)` is the *constant* `constHom (dMid k)`.
Applying `Φ` gives `Φ(e) := phiTowerD (endUp E) : D (k+1) → D (k+2)` and dually,
and the ep-pair laws come out of ingredient 2 alone:

* **retraction** — `endDown ∘ endUp = id` on the nose (two uses of `p ∘ e = id`),
  so `Φ(p) ∘ Φ(e) = Φ(id) = id` by `phiTower_comp` and `phiTower_id`.  No
  computation with the glue at all.
* **deflation** — `endUp ∘ endDown ≤ id` pointwise (two uses of `e ∘ p ≤ id`),
  and `Φ` is monotone in its morphism argument
  (`baseMapGen_leGlueGen_of_le` composed with `leGlueGen_canon`), so
  `Φ(e) ∘ Φ(p) ≤ Φ(id) = id`.
* **tripointed again** — `phiTower_triBot` / `_triMark` / `_triTop`, so the
  recursion stays inside the category it started in.

## The base

`iotaD 0` cannot start the recursion — it misses `⊤`, which is obstruction (T)'s
one line.  **`(glueAA 0, qAA 0)` can**: §82 proved it is an ep-pair and §83
proved it is tripointed.  So the tower starts one level up, at `D 1`, which
costs nothing — a tower and its shift have the same bilimit (`TowerShift`).

## What is gained

```lean
emb_succ (n) : (iter (n+1)).emb = phiTowerD (iter n).endUp
```

— by `rfl`.  **The shifted tower is `Φ` applied to the tower**, which is exactly
the hypothesis the bilimit self-similarity argument consumes and which
`fTowerReal` does not satisfy.
-/

open scoped Classical

namespace PhiIterateTower

open GlueAAJoin GlueAAEpPartner FTowerTripointed PhiTriFunctor PhiTriTower GenContinuity

/-! ## Tripointed ep-pairs between consecutive levels -/

/-- An embedding/projection pair `D k ⇄ D (k+1)` whose embedding preserves all
three marked points.  This is the data `Φ` acts on. -/
structure TriEP (k : ℕ) where
  emb : D k → D (k + 1)
  prj : D (k + 1) → D k
  emb_mono : Monotone emb
  prj_mono : Monotone prj
  retraction : ∀ x, prj (emb x) = x
  deflation : ∀ z, emb (prj z) ≤ z
  emb_bot : emb ⊥ = ⊥
  emb_mid : emb (dMid k) = dMid (k + 1)
  emb_top : emb ⊤ = ⊤

namespace TriEP

variable {k : ℕ} (E : TriEP k)

theorem prj_bot : E.prj (⊥ : D (k + 1)) = ⊥ := by
  rw [← E.emb_bot, E.retraction]

theorem prj_mid : E.prj (dMid (k + 1)) = dMid k := by
  rw [← E.emb_mid, E.retraction]

theorem prj_top : E.prj (⊤ : D (k + 1)) = ⊤ := by
  rw [← E.emb_top, E.retraction]

/-! ### The two `End` actions -/

noncomputable def endUpFun (h : EndP (D k)) : EndP (D (k + 1)) :=
  ⟨fun x => E.emb (h (E.prj x)),
    fun _ _ hxy => E.emb_mono (h.monotone (E.prj_mono hxy))⟩

theorem endUpFun_mono : Monotone E.endUpFun := by
  intro h h' hh
  rw [OrderHom.le_def]
  intro x
  exact E.emb_mono (OrderHom.le_def.mp hh (E.prj x))

noncomputable def endDownFun (h : EndP (D (k + 1))) : EndP (D k) :=
  ⟨fun x => E.prj (h (E.emb x)),
    fun _ _ hxy => E.prj_mono (h.monotone (E.emb_mono hxy))⟩

theorem endDownFun_mono : Monotone E.endDownFun := by
  intro h h' hh
  rw [OrderHom.le_def]
  intro x
  exact E.prj_mono (OrderHom.le_def.mp hh (E.emb x))

/-- `h ↦ e ∘ h ∘ p`, tripointed because `e` is and the marked point of
`EndP (D k)` is a constant. -/
noncomputable def endUp : TowerHom k (k + 1) where
  toFun := ⟨E.endUpFun, E.endUpFun_mono⟩
  map_bot := by
    ext x
    show E.emb ((⊥ : EndP (D k)) (E.prj x)) = (⊥ : EndP (D (k + 1))) x
    rw [endPBot_apply, endPBot_apply, E.emb_bot]
  map_mark := by
    ext x
    show E.emb ((markedPt k) (E.prj x)) = (markedPt (k + 1)) x
    rw [markedPt_apply, markedPt_apply, E.emb_mid]
  map_top := by
    ext x
    show E.emb ((⊤ : EndP (D k)) (E.prj x)) = (⊤ : EndP (D (k + 1))) x
    rw [endPTop_apply, endPTop_apply, E.emb_top]

/-- `h ↦ p ∘ h ∘ e`, tripointed for the dual reasons. -/
noncomputable def endDown : TowerHom (k + 1) k where
  toFun := ⟨E.endDownFun, E.endDownFun_mono⟩
  map_bot := by
    ext x
    show E.prj ((⊥ : EndP (D (k + 1))) (E.emb x)) = (⊥ : EndP (D k)) x
    rw [endPBot_apply, endPBot_apply, E.prj_bot]
  map_mark := by
    ext x
    show E.prj ((markedPt (k + 1)) (E.emb x)) = (markedPt k) x
    rw [markedPt_apply, markedPt_apply, E.prj_mid]
  map_top := by
    ext x
    show E.prj ((⊤ : EndP (D (k + 1))) (E.emb x)) = (⊤ : EndP (D k)) x
    rw [endPTop_apply, endPTop_apply, E.prj_top]

/-! ### The two composites, before `Φ` -/

theorem endDown_endUp : (E.endDown.comp E.endUp).toFun = (TriHom.id (markedPt k)).toFun := by
  ext h x
  show E.prj (E.emb (h (E.prj (E.emb x)))) = h x
  rw [E.retraction, E.retraction]

theorem endUp_endDown_le :
    (E.endUp.comp E.endDown).toFun ≤ (TriHom.id (markedPt (k + 1))).toFun := by
  intro h
  rw [OrderHom.le_def]
  intro y
  show E.emb (E.prj (h (E.emb (E.prj y)))) ≤ h y
  exact le_trans (E.deflation _) (h.monotone (E.deflation y))

end TriEP

/-! ## `Φ` is monotone in its morphism argument -/

theorem phiTower_le_of_le {k k' : ℕ} {f g : TowerHom k k'} (h : f.toFun ≤ g.toFun)
    (x : D (k + 1)) : phiTowerD f x ≤ phiTowerD g x :=
  leGlueGen_canon (markedPt k') ((D_marked_point_nondegenerate k').1)
    ((D_marked_point_nondegenerate k').2.1) ((D_marked_point_nondegenerate k').2.2)
    (baseMapGen_leGlueGen_of_le (markedPt k') h x.1)

theorem phiTower_congr {k k' : ℕ} {f g : TowerHom k k'} (h : f.toFun = g.toFun)
    (x : D (k + 1)) : phiTowerD f x = phiTowerD g x := by
  refine Subtype.ext ?_
  show canonGen (markedPt k') (baseMapGen f.toFun x.1)
    = canonGen (markedPt k') (baseMapGen g.toFun x.1)
  rw [h]

/-! ## The step -/

section Step

variable {k : ℕ} (E : TriEP k)

theorem step_retraction (z : D (k + 1)) :
    phiTowerD E.endDown (phiTowerD E.endUp z) = z := by
  have hc := phiTower_comp E.endUp E.endDown
  have h1 : phiTowerD (E.endDown.comp E.endUp) z = phiTowerD E.endDown (phiTowerD E.endUp z) := by
    show phiTower (E.endDown.comp E.endUp) z = _
    rw [hc]
    rfl
  rw [← h1, phiTower_congr E.endDown_endUp z]
  show phiTower (TriHom.id (markedPt k)) z = z
  rw [phiTower_id k]
  rfl

theorem step_deflation (z : D (k + 2)) :
    phiTowerD E.endUp (phiTowerD E.endDown z) ≤ z := by
  have hc := phiTower_comp E.endDown E.endUp
  have h1 : phiTowerD (E.endUp.comp E.endDown) z = phiTowerD E.endUp (phiTowerD E.endDown z) := by
    show phiTower (E.endUp.comp E.endDown) z = _
    rw [hc]
    rfl
  have h2 : phiTowerD (E.endUp.comp E.endDown) z
      ≤ phiTowerD (TriHom.id (markedPt (k + 1))) z :=
    phiTower_le_of_le E.endUp_endDown_le z
  have h3 : phiTowerD (TriHom.id (markedPt (k + 1))) z = z := by
    show phiTower (TriHom.id (markedPt (k + 1))) z = z
    rw [phiTower_id (k + 1)]
    rfl
  rw [← h1]
  exact le_of_le_of_eq h2 h3

/-- **`Φ` of a tripointed ep-pair is a tripointed ep-pair.** -/
noncomputable def phiStep : TriEP (k + 1) where
  emb := phiTowerD E.endUp
  prj := phiTowerD E.endDown
  emb_mono := fun _ _ h => phiTower_monotone E.endUp h
  prj_mono := fun _ _ h => phiTower_monotone E.endDown h
  retraction := step_retraction E
  deflation := step_deflation E
  emb_bot := by
    rw [PhiTriTower.bot_succ_eq k, PhiTriTower.bot_succ_eq (k + 1)]
    exact phiTower_triBot E.endUp
  emb_mid := by
    rw [PhiTriTower.dMid_succ_eq k, PhiTriTower.dMid_succ_eq (k + 1)]
    exact phiTower_triMark E.endUp
  emb_top := by
    rw [PhiTriTower.top_succ_eq k, PhiTriTower.top_succ_eq (k + 1)]
    exact phiTower_triTop E.endUp

end Step

/-! ## The base, and the tower -/

/-- The recursion starts at `D 1`.  `iotaD 0` cannot start it — it misses `⊤`
(obstruction (T)) — but `(glueAA 0, qAA 0)` is a tripointed ep-pair by §82/§83. -/
noncomputable def baseEP : TriEP 1 where
  emb := glueAA 0
  prj := qAA 0
  emb_mono := fun _ _ h => glueAA_monotone 0 h
  prj_mono := EpFromJoin.upper_monotone (glueAA 0) (GlueAAEpPartner.glueAA_bot 0)
    (glueAAJoinPreserving 0)
  retraction := qAA_glueAA 0
  deflation := EpFromJoin.map_upper_le (glueAA 0) (GlueAAEpPartner.glueAA_bot 0)
    (glueAAJoinPreserving 0)
  emb_bot := GlueAAEpPartner.glueAA_bot 0
  emb_mid := glueAA_mid 0
  emb_top := glueAA_top 0

/-- The iterates: `iter 0` is the base, `iter (n+1)` is `Φ` of `iter n`. -/
noncomputable def iter : (n : ℕ) → TriEP (n + 1)
  | 0 => baseEP
  | n + 1 => phiStep (iter n)

/-- **The `Φ`-iterate tower.** -/
noncomputable def phiTowerEP : EpPairTower where
  carrier n := D (n + 1)
  order n := inferInstance
  emb n := (iter n).emb
  prj n := (iter n).prj
  emb_mono n := (iter n).emb_mono
  prj_mono n := (iter n).prj_mono
  retraction n := (iter n).retraction
  deflation n := (iter n).deflation

@[simp] theorem phiTowerEP_carrier (n : ℕ) : phiTowerEP.carrier n = D (n + 1) := rfl

@[simp] theorem phiTowerEP_emb (n : ℕ) : phiTowerEP.emb n = (iter n).emb := rfl

/-- **Every embedding is `Φ` of the previous one** — the property the whole
construction exists for, and the one `fTowerReal` fails (§83). -/
theorem emb_succ (n : ℕ) : (iter (n + 1)).emb = phiTowerD (iter n).endUp := rfl

/-- …and every projection is `Φ` of the previous one. -/
theorem prj_succ (n : ℕ) : (iter (n + 1)).prj = phiTowerD (iter n).endDown := rfl

/-- The tower is tripointed at every level. -/
theorem emb_tripointed (n : ℕ) :
    (iter n).emb (⊥ : D (n + 1)) = ⊥
      ∧ (iter n).emb (dMid (n + 1)) = dMid (n + 2)
      ∧ (iter n).emb (⊤ : D (n + 1)) = ⊤ :=
  ⟨(iter n).emb_bot, (iter n).emb_mid, (iter n).emb_top⟩

end PhiIterateTower
